module

public import StacksFrontier.AlgebraicGeometry.Stacks.CartesianAffinePresentation

/-!
# Kernels stay cartesian along flat morphisms

Let `φ : ℱ ⟶ 𝒢` be a map of `𝒪_𝒳`-modules on a category fibred in groupoids over the big fppf
site and `g : y ⟶ x` a morphism along which the base change comparisons
`𝒪(y) ⊗_{𝒪(x)} ℱ(x) ⟶ ℱ(y)` and `𝒪(y) ⊗_{𝒪(x)} 𝒢(x) ⟶ 𝒢(y)` are bijective. If `𝒪(x) ⟶ 𝒪(y)`
is flat, then the base change comparison of `Ker φ` along `g` is bijective as well: tensoring
with a flat algebra is exact. This is the flat base change of kernels used in the proof of
Stacks 0GR9 (and the reason `Ker φ` lies in `LQCoh^{fbc}`, Stacks 0765).

The file also records the two algebraic steps of a finite presentation by base change, for a
generating family of a module and a generating family of its relations.

## Main results

* `Module.BaseChange.bijective_liftBaseChange_of_exact`: flat base change of a kernel.
* `Module.BaseChange.exists_finsupp_of_surjective_liftBaseChange_of_span` and
  `Module.BaseChange.exists_finsupp_relations_of_bijective_liftBaseChange_of_span`.
* `AlgebraicGeometry.Stack.bijective_fibredSectionsBaseChange_kernel`.

## References

* [Stacks Project, Tag 00HJ](https://stacks.math.columbia.edu/tag/00HJ)
* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v w

namespace Module.BaseChange

variable {A Bc : Type*} [CommRing A] [CommRing Bc] [Algebra A Bc]

section Kernel

variable {KT FT GT KW FW GW : Type*}
  [AddCommGroup KT] [Module A KT] [AddCommGroup FT] [Module A FT] [AddCommGroup GT] [Module A GT]
  [AddCommGroup KW] [Module A KW] [Module Bc KW] [IsScalarTower A Bc KW]
  [AddCommGroup FW] [Module A FW] [Module Bc FW] [IsScalarTower A Bc FW]
  [AddCommGroup GW] [Module A GW] [Module Bc GW] [IsScalarTower A Bc GW]
  (iT : KT →ₗ[A] FT) (φT : FT →ₗ[A] GT) (iW : KW →ₗ[Bc] FW) (φW : FW →ₗ[Bc] GW)
  (rK : KT →ₗ[A] KW) (rF : FT →ₗ[A] FW) (rG : GT →ₗ[A] GW)

/-- Linear maps compatible with restriction commute with the base change comparisons. -/
private theorem liftBaseChange_comm {P Q P' Q' : Type*} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] [AddCommGroup P'] [Module A P'] [Module Bc P']
    [IsScalarTower A Bc P'] [AddCommGroup Q'] [Module A Q'] [Module Bc Q'] [IsScalarTower A Bc Q']
    (u : P' →ₗ[Bc] Q') (rP : P →ₗ[A] P') (rQ : Q →ₗ[A] Q') (h : P →ₗ[A] Q)
    (hsq : ∀ m, u (rP m) = rQ (h m)) (ζ : Bc ⊗[A] P) :
    u (rP.liftBaseChange Bc ζ) = rQ.liftBaseChange Bc (h.lTensor Bc ζ) := by
  induction ζ using TensorProduct.induction_on with
  | zero => simp
  | tmul b k => simp [hsq]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **Flat base change of a kernel.** Given exact sequences `0 → K_T → F_T → G_T` over `A` and
`0 → K_W → F_W → G_W` over a flat `A`-algebra `B` and compatible restriction maps, if the base
change comparisons of `F` and `G` are bijective (injective suffices for `G`), so is that of `K`. -/
theorem bijective_liftBaseChange_of_exact [Module.Flat A Bc]
    (hiT : Function.Injective iT) (hT : Function.Exact iT φT)
    (hiW : Function.Injective iW) (hW : Function.Exact iW φW)
    (hsqi : ∀ k, iW (rK k) = rF (iT k)) (hsqφ : ∀ m, φW (rF m) = rG (φT m))
    (hF : Function.Bijective (rF.liftBaseChange Bc))
    (hG : Function.Injective (rG.liftBaseChange Bc)) :
    Function.Bijective (rK.liftBaseChange Bc) := by
  have hci := liftBaseChange_comm iW rK rF iT hsqi
  have hcφ := liftBaseChange_comm φW rF rG φT hsqφ
  refine ⟨fun a b hab ↦ Module.Flat.lTensor_preserves_injective_linearMap iT hiT (hF.1 ?_),
    fun k ↦ ?_⟩
  · rw [← hci, ← hci, hab]
  · obtain ⟨ζ, hζ⟩ := hF.2 (iW k)
    have h0 : φT.lTensor Bc ζ = 0 := hG (by
      rw [← hcφ, hζ, map_zero, (hW (iW k)).2 ⟨k, rfl⟩])
    obtain ⟨ξ, rfl⟩ := (Module.Flat.lTensor_exact Bc hT ζ).1 h0
    exact ⟨ξ, hiW ((hci ξ).trans hζ)⟩

end Kernel

section Span

variable {NT NW : Type*} [AddCommGroup NT] [Module A NT] [AddCommGroup NW] [Module A NW]
  [Module Bc NW] [IsScalarTower A Bc NW] (rN : NT →ₗ[A] NW)

/-- A linear map sends the span of a family over `A` into the span of the image family over `B`. -/
private theorem map_mem_span_range_restrictScalars {M N I : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module Bc N] [IsScalarTower A Bc N] (f : M →ₗ[A] N)
    (s : I → M) {x : M} (hx : x ∈ Submodule.span A (Set.range s)) :
    f x ∈ Submodule.span Bc (Set.range fun i ↦ f (s i)) := by
  have := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_span, ← Set.range_comp] at this
  exact Submodule.span_le_restrictScalars A Bc _ this

/-- If the base change comparison of `rN` is surjective and the `s i` span, every element of the
target is a combination of the images of the `s i`. -/
theorem exists_finsupp_of_surjective_liftBaseChange_of_span {I : Type*} (s : I → NT)
    (hs : Submodule.span A (Set.range s) = ⊤)
    (h : Function.Surjective (rN.liftBaseChange Bc)) (m : NW) :
    ∃ c : I →₀ Bc, (c.sum fun i r ↦ r • rN (s i)) = m := by
  rw [← Finsupp.mem_span_range_iff_exists_finsupp]
  obtain ⟨ζ, rfl⟩ := h m
  have hrN : ∀ n : NT, rN n ∈ Submodule.span Bc (Set.range fun i ↦ rN (s i)) := fun n ↦
    map_mem_span_range_restrictScalars rN s (hs ▸ Submodule.mem_top)
  induction ζ using TensorProduct.induction_on with
  | zero => simp
  | tmul b n =>
    rw [LinearMap.liftBaseChange_tmul]
    exact Submodule.smul_mem _ b (hrN n)
  | add a b ha hb =>
    rw [map_add]
    exact add_mem ha hb

/-- **Right exactness of base change, for generators and generating relations.** If the base
change comparison of `rN` is bijective, the `s i` span and the `ρ k` span the relations among
them, then every relation among the images of the `s i` is a combination of the images of the
`ρ k`. -/
theorem exists_finsupp_relations_of_bijective_liftBaseChange_of_span {I K : Type*}
    (s : I → NT) (hs : Submodule.span A (Set.range s) = ⊤) (ρ : K → I →₀ A)
    (hρ : Submodule.span A (Set.range ρ) = LinearMap.ker (Finsupp.linearCombination A s))
    (h : Function.Bijective (rN.liftBaseChange Bc)) (c : I →₀ Bc)
    (hc : (c.sum fun i r ↦ r • rN (s i)) = 0) :
    ∃ d : K →₀ Bc, c = d.sum fun k r ↦ r • (ρ k).mapRange (algebraMap A Bc) (map_zero _) := by
  classical
  let bT : (I →₀ A) →ₗ[A] NT := Finsupp.linearCombination A s
  let bW : (I →₀ Bc) →ₗ[Bc] NW := Finsupp.linearCombination Bc (fun i ↦ rN (s i))
  let rP : (I →₀ A) →ₗ[A] (I →₀ Bc) := Finsupp.mapRange.linearMap (Algebra.linearMap A Bc)
  have hsqb : ∀ q, rN (bT q) = bW (rP q) := by
    intro q
    simp only [bT, bW, rP, Finsupp.linearCombination_apply, Finsupp.mapRange.linearMap_apply,
      map_finsuppSum, map_smul]
    rw [Finsupp.sum_mapRange_index (h := fun i a ↦ a • rN (s i)) (fun _ ↦ zero_smul _ _)]
    exact Finset.sum_congr rfl fun i _ ↦ (algebraMap_smul Bc (q i) (rN (s i))).symm
  have hP : Function.Surjective (rP.liftBaseChange Bc) :=
    (Module.BaseChange.bijective_liftBaseChange_of_basis (Finsupp.basisSingleOne)
      (Finsupp.basisSingleOne) rP fun i ↦ by
        simp [rP, Finsupp.mapRange_single]).2
  have hbT : Function.Surjective bT := by
    rwa [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  have hmem := Module.BaseChange.mem_span_image_ker_of_liftBaseChange bT bW rP rN hsqb hP h.1 hbT
    (z := c) (by simpa [bW, Finsupp.linearCombination_apply] using hc)
  have hle : Submodule.span Bc (rP '' (LinearMap.ker bT : Set (I →₀ A))) ≤
      Submodule.span Bc (Set.range fun k ↦ rP (ρ k)) := by
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, rfl⟩
    exact map_mem_span_range_restrictScalars rP ρ (hρ ▸ hq)
  exact (Finsupp.mem_span_range_iff_exists_finsupp.1 (hle hmem)).imp fun _ ↦ Eq.symm

end Span

end Module.BaseChange

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)

/-- **Kernels stay cartesian along flat morphisms.** If the base change comparisons of `ℱ` and
`𝒢` along `g : y ⟶ x` are bijective and `𝒪(x) ⟶ 𝒪(y)` is flat, then the base change comparison
of the kernel of `φ : ℱ ⟶ 𝒢` along `g` is bijective. -/
theorem bijective_fibredSectionsBaseChange_kernel
    {F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)}
    (φ : F ⟶ G) {x y : 𝒳} (g : y ⟶ x)
    (hF : Function.Bijective (fibredSectionsBaseChange hp F g))
    (hG : Function.Bijective (fibredSectionsBaseChange hp G g))
    (hflat : letI := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) g
      Module.Flat (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y)) :
    Function.Bijective (fibredSectionsBaseChange hp (kernel φ) g) := by
  let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) g
  let := fibredSectionsModule hp F x
  let := fibredSectionsModule hp F y
  let := fibredSectionsModuleOver hp F g
  let := fibredSectionsModule hp G x
  let := fibredSectionsModule hp G y
  let := fibredSectionsModuleOver hp G g
  let := fibredSectionsModule hp (kernel φ) x
  let := fibredSectionsModule hp (kernel φ) y
  let := fibredSectionsModuleOver hp (kernel φ) g
  have : IsScalarTower (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y)
      (F.val.obj (op y)) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y)
      (G.val.obj (op y)) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y)
      ((kernel φ).val.obj (op y)) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let iT : (kernel φ).val.obj (op x) →ₗ[fibredSectionRing B S hS p x] F.val.obj (op x) :=
    ((kernel.ι φ).val.app (op x)).hom
  let φT : F.val.obj (op x) →ₗ[fibredSectionRing B S hS p x] G.val.obj (op x) :=
    (φ.val.app (op x)).hom
  let iW : (kernel φ).val.obj (op y) →ₗ[fibredSectionRing B S hS p y] F.val.obj (op y) :=
    ((kernel.ι φ).val.app (op y)).hom
  let φW : F.val.obj (op y) →ₗ[fibredSectionRing B S hS p y] G.val.obj (op y) :=
    (φ.val.app (op y)).hom
  have hex : ∀ z : 𝒳, Function.Exact ((kernel.ι φ).val.app (op z)) (φ.val.app (op z)) :=
    fun z m ↦ ⟨SheafOfModules.exists_kernel_val_app φ (op z) m, by
      rintro ⟨k, rfl⟩
      exact congrArg (fun f ↦ f.val.app (op z) k) (kernel.condition φ) |>.trans rfl⟩
  exact Module.BaseChange.bijective_liftBaseChange_of_exact iT φT iW φW
    (fibredSectionsRestrict hp (kernel φ) g) (fibredSectionsRestrict hp F g)
    (fibredSectionsRestrict hp G g)
    (SheafOfModules.kernel_ι_val_app_injective φ (op x)) (hex x)
    (SheafOfModules.kernel_ι_val_app_injective φ (op y)) (hex y)
    (fun k ↦ (congrArg (fun f ↦ f k) (congrArg ConcreteCategory.hom
      ((kernel.ι φ).val.naturality g.op))))
    (fun m ↦ (congrArg (fun f ↦ f m) (congrArg ConcreteCategory.hom
      (φ.val.naturality g.op))))
    hF hG.1

end AlgebraicGeometry.Stack

end
