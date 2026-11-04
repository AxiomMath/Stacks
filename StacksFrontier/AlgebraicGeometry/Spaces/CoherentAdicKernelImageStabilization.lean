module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartBijectivePropagation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionExact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernelImage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernelStabilization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentArtinRees
public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivityFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleSectionsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAffineComparison

/-!
# Stabilization of the kernel images of a morphism of coherent adic systems on an algebraic space

Let `F` be a Noetherian algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a quasi-coherent
sheaf of ideals on its small étale ringed site and let `α : E ⟶ E'` be a morphism of coherent
`𝓘`-adic systems.  The kernel of `α` in `Coh(F, 𝓘)` is assembled from the kernel images
`AlgebraicGeometry.Space.kernelImageAt`, the subobjects of `E_m` cut out by the kernels of `α` at
the higher levels `l ≥ m`. This file proves that these kernel images stabilize, as subsheaves of
`E_m`.

## Main results

* `AlgebraicGeometry.Space.range_val_app_kernelImageAtIncl`: the sections of a kernel image over
  an affine chart are the image of the kernel of `α` on sections at the higher level.
* `AlgebraicGeometry.Space.kernelImages_eventuallyConstant`: for each level `m` there is a
  constant `c` such that for every `l ≥ m + c` the kernel image in `E_m` computed from level `l`
  is identified, over `E_m`, with the one computed from level `m + c`.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: the term at `n` is the Stacks source's
`E_{n + 1}`.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 07UL](https://stacks.math.columbia.edu/tag/07UL)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Sections of a kernel and of an image -/

/-- The sections of a kernel of a morphism of `𝒪_F`-modules over a chart are the kernel of the
morphism on sections there. -/
theorem range_val_app_kernel_ι {M N : Modules.{u, u} B S hS F hF} (g : M ⟶ N)
    (V : SmallEtale B S hS F) :
    LinearMap.range ((kernel.ι g).val.app (op V)).hom =
      LinearMap.ker (g.val.app (op V)).hom := by
  refine SetLike.ext fun x => ?_
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  exact (SheafOfModules.exact_kernel_ι_val_app g (op V) x).symm

/-- A morphism of `𝒪_F`-modules factors through its image on the sections over any chart. -/
theorem val_app_image_ι_val_app_factorThruImage {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (V : SmallEtale B S hS F) (x : M.val.obj (op V)) :
    ((Abelian.image.ι f).val.app (op V)) (((Abelian.factorThruImage f).val.app (op V)) x) =
      (f.val.app (op V)) x :=
  congrArg (fun φ : M ⟶ N => (φ.val.app (op V)) x) (Abelian.image.fac f)

/-- The sections over an affine chart of the image of a morphism of `𝒪_F`-modules cartesian on
affine charts are the range of the morphism on sections there. -/
theorem range_val_app_image_ι {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N)
    (V : SmallEtale B S hS F)
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    LinearMap.range ((Abelian.image.ι f).val.app (op V)).hom =
      LinearMap.range (f.val.app (op V)).hom := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := surjective_val_app_factorThruImage_of_cartesian f hM hN V hV y
    refine ⟨x, ?_⟩
    rw [← val_app_image_ι_val_app_factorThruImage B S hS F hF f V x]
    exact congrArg ((Abelian.image.ι f).val.app (op V)) hx
  · rintro _ ⟨x, rfl⟩
    exact ⟨((Abelian.factorThruImage f).val.app (op V)) x,
      val_app_image_ι_val_app_factorThruImage B S hS F hF f V x⟩

/-! ### Bijectivity on sections from equality of ranges -/

/-- Two subobjects of an `𝒪_F`-module with the same sections over a chart are identified there by
any morphism lying over their inclusions. -/
theorem bijective_val_app_of_range_eq {P Q T : Modules.{u, u} B S hS F hF}
    {p : P ⟶ T} {q : Q ⟶ T} [Mono p] [Mono q] (j : P ⟶ Q) (hj : j ≫ q = p)
    (V : SmallEtale B S hS F)
    (hrange : LinearMap.range (p.val.app (op V)).hom =
      LinearMap.range (q.val.app (op V)).hom) :
    Function.Bijective (j.val.app (op V)) := by
  have hfac : ∀ x, (q.val.app (op V)) ((j.val.app (op V)) x) = (p.val.app (op V)) x := fun x =>
    congrArg (fun φ : P ⟶ T => (φ.val.app (op V)) x) hj
  refine ⟨fun x y hxy => injective_val_app_of_mono B S hS p (op V) ?_, fun y => ?_⟩
  · exact (hfac x).symm.trans ((congrArg (q.val.app (op V)) hxy).trans (hfac y))
  · obtain ⟨x, hx⟩ := hrange.ge (LinearMap.mem_range_self (q.val.app (op V)).hom y)
    exact ⟨x, injective_val_app_of_mono B S hS q (op V) ((hfac x).trans hx)⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-! ### The kernel images, chartwise -/

/-- The kernel of a morphism of coherent adic systems at a level is cartesian on affine
charts. -/
theorem isCartesianOnAffineCharts_kernel_app (α : E ⟶ E') (l : ℕ) :
    IsCartesianOnAffineCharts (kernel (α.hom.app (op l))) :=
  isCartesianOnAffineCharts_kernel _
    (isCartesianOnAffineCharts_of_isCoherentAdicSystem B S hS F hF 𝓘 E.property l)
    (isCartesianOnAffineCharts_of_isCoherentAdicSystem B S hS F hF 𝓘 E'.property l)

/-- Every kernel image of a morphism of coherent adic systems is cartesian on affine charts. -/
theorem isCartesianOnAffineCharts_kernelImageAt (α : E ⟶ E') (m l : ℕ) (h : m ≤ l) :
    IsCartesianOnAffineCharts (kernelImageAt B S hS F hF 𝓘 α m l h) :=
  isCartesianOnAffineCharts_image_of_cartesian _
    (isCartesianOnAffineCharts_kernel_app B S hS F hF 𝓘 α l)
    (isCartesianOnAffineCharts_of_isCoherentAdicSystem B S hS F hF 𝓘 E.property m)

/-- The sections of a kernel image over an affine chart are the image, under the transition map
on sections, of the kernel of `α` on the sections at the higher level. -/
theorem range_val_app_kernelImageAtIncl (α : E ⟶ E') (m l : ℕ) (h : m ≤ l)
    (V : SmallEtale B S hS F)
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    LinearMap.range ((kernelImageAtIncl B S hS F hF 𝓘 α m l h).val.app (op V)).hom =
      Submodule.map ((E.obj.map (homOfLE h).op).val.app (op V)).hom
        (LinearMap.ker ((α.hom.app (op l)).val.app (op V)).hom) := by
  have h₁ : LinearMap.range ((kernelImageAtIncl B S hS F hF 𝓘 α m l h).val.app (op V)).hom =
      LinearMap.range ((kernel.ι (α.hom.app (op l)) ≫
        E.obj.map (homOfLE h).op).val.app (op V)).hom :=
    range_val_app_image_ι B S hS F hF _
      (isCartesianOnAffineCharts_kernel_app B S hS F hF 𝓘 α l)
      (isCartesianOnAffineCharts_of_isCoherentAdicSystem B S hS F hF 𝓘 E.property m) V hV
  have h₂ : ((kernel.ι (α.hom.app (op l)) ≫ E.obj.map (homOfLE h).op).val.app (op V)).hom =
      ((E.obj.map (homOfLE h).op).val.app (op V)).hom.comp
        ((kernel.ι (α.hom.app (op l))).val.app (op V)).hom := rfl
  refine h₁.trans ((congrArg LinearMap.range h₂).trans ?_)
  rw [LinearMap.range_comp]
  exact congrArg (Submodule.map ((E.obj.map (homOfLE h).op).val.app (op V)).hom)
    (range_val_app_kernel_ι B S hS F hF _ V)

/-! ### The global stabilization -/

/-- Let `α` be a morphism of coherent adic systems on a Noetherian algebraic space. For a level
`m` there is a constant `c` such that for every `l ≥ m + c` the kernel image in `E_m` computed
from level `l` agrees with the one computed from level `m + c`, by an isomorphism commuting with
their inclusions into `E_m`. -/
theorem kernelImages_eventuallyConstant (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (α : E ⟶ E') (m : ℕ) :
    ∃ c : ℕ, ∀ l : ℕ, ∀ h : m + c ≤ l,
      ∃ e : kernelImageAt B S hS F hF 𝓘 α m l ((Nat.le_add_right m c).trans h) ≅
          kernelImageAt B S hS F hF 𝓘 α m (m + c) (Nat.le_add_right m c),
        e.hom ≫ kernelImageAtIncl B S hS F hF 𝓘 α m (m + c) (Nat.le_add_right m c) =
          kernelImageAtIncl B S hS F hF 𝓘 α m l ((Nat.le_add_right m c).trans h) := by
  classical
  obtain ⟨U₀, f₀, hU₀aff, hU₀surj, hU₀et⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).1 hN.1
  let U : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk f₀, presheaf_etale_of_isEtale B S hS hU₀et⟩
  have hUaff : IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) := hU₀aff
  have hUsurj : IsSurjective B S hS U.1.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U₀ f₀).1 hU₀surj
  obtain ⟨Sv, hSv, hfac⟩ := exists_covering_through_noetherianAffine B S hS F hF hN.2.2 U
  obtain ⟨ι, hιfin, V, fV, -, hVle, hVcov⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS F U hUaff Sv hSv
  choose A lift mc hA hfactor using fun i => hfac (fV i) (hVle _ (Sieve.ofArrows_mk V fV i))
  have hAaff : ∀ i, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (A i)) :=
    fun i => (hA i).1
  have hAcov : Sieve.ofArrows A mc ∈ SmallEtale.topology B S hS F U := by
    refine (SmallEtale.topology B S hS F).superset_covering ?_ hVcov
    rintro Y k ⟨W', t, p, ⟨i⟩, hcomp⟩
    refine ⟨A i, t ≫ lift i, mc i, ⟨i⟩, ?_⟩
    rwa [Category.assoc, ← hfactor i]
  have hAtop := ofObjects_mem_topology_of_ofArrows B S hS F hF hUsurj A mc hAcov
  have hcc : ∀ i, ∃ c : ℕ, ∀ l : ℕ, ∀ h : m + c ≤ l,
      Submodule.map ((E.obj.map (homOfLE ((Nat.le_add_right m c).trans h)).op).val.app
            (op (A i))).hom
          (LinearMap.ker ((α.hom.app (op l)).val.app (op (A i))).hom) =
        Submodule.map ((E.obj.map (homOfLE (Nat.le_add_right m c)).op).val.app (op (A i))).hom
          (LinearMap.ker ((α.hom.app (op (m + c))).val.app (op (A i))).hom) := fun i =>
    exists_chartSectionsKernelImage_eventuallyConstant B S hS F hF 𝓘 E.property E'.property
      hIcart (hA i) α.hom m
  choose ci hci using hcc
  let _ := Fintype.ofFinite ι
  let d := Finset.univ.sup ci
  have hd : ∀ i, ci i ≤ d := fun i => Finset.le_sup (f := ci) (Finset.mem_univ i)
  refine ⟨d, fun l h => ?_⟩
  obtain ⟨j, hj⟩ := kernelImageAt_hasMap B S hS F hF 𝓘 α m (m + d) l (Nat.le_add_right m d) h
  have hbijA : ∀ i, Function.Bijective (j.val.app (op (A i))) := by
    intro i
    refine bijective_val_app_of_range_eq B S hS F hF j hj (A i) ?_
    rw [range_val_app_kernelImageAtIncl B S hS F hF 𝓘 α m l _ (A i) (hAaff i),
      range_val_app_kernelImageAtIncl B S hS F hF 𝓘 α m (m + d) _ (A i) (hAaff i),
      hci i l (by have := hd i; omega), hci i (m + d) (by have := hd i; omega)]
  have hiso : IsIso j := by
    have hPcart := isCartesianOnAffineCharts_kernelImageAt B S hS F hF 𝓘 α m l
      ((Nat.le_add_right m d).trans h)
    have hQcart := isCartesianOnAffineCharts_kernelImageAt B S hS F hF 𝓘 α m (m + d)
      (Nat.le_add_right m d)
    refine Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map hAtop j fun i => ?_
    refine SmallEtale.isIso_of_bijective_app_of_isAffine B S hS F hF (A i) _ fun Z hZaff => ?_
    exact bijective_val_app_of_bijective_of_cartesian B S hS F hF j hPcart hQcart
      (hAaff i) hZaff Z.hom (hbijA i)
  exact ⟨asIso j, hj⟩

end AlgebraicGeometry.Space

end
