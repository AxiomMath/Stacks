module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftTorsors
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Maps extending a given map along a monomorphism

Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence in an abelian category and let
`c : X₁ ⟶ M` be a map. The maps `d : X₂ ⟶ M` with `d|_{X₁} = c` form, as soon as there is one, a
principal homogeneous space under `Hom(X₃, M)`, an element `φ` acting by `d ↦ d - (X₂ ⟶ X₃) ≫ φ`.
When `c` is an epimorphism, such a `d` is determined by its kernel, and the kernels that occur are
exactly the subobjects of `X₂` which map onto `X₃` and meet `X₁` in the kernel of `c`.

This is the linear algebra behind Stacks 0CZV: for a quotient `ℱ ⟶ 𝒬` with kernel `𝒦` and a flat
module `ℱ'` over a first order thickening reducing to `ℱ`, the lifts of the quotient are the
kernels of the maps `π⁻¹(𝒦) ⟶ 𝒬 ⊗ 𝒥` extending the canonical map `I·ℱ' ⟶ 𝒬 ⊗ 𝒥`, and the
remark's action of `Hom(𝒦, 𝒬 ⊗ 𝒥)` is the action above.

## Main definitions

* `Deformation.ToposThickening.ExtensionAlong`: the maps `d : X₂ ⟶ M` with `X₁ ⟶ X₂ ⟶ M = c`.
* `Deformation.ToposThickening.IsExtensionKernel`: the subobjects of `X₂` mapping onto `X₃` and
  meeting `X₁` in the kernel of `c`.
* `Deformation.ToposThickening.extensionAlongKernelEquiv`: taking kernels is a bijection between
  the two.

* `Deformation.ToposThickening.extensionKernelIn`, `Deformation.ToposThickening.extensionInclusion`
  and `Deformation.ToposThickening.extensionDeformation`: for `X₂ ⊂ F`, the subobject `K' ⊂ F` cut
  out by `d`, the inclusion `M ⊂ F/K'`, and the remark's deformed subobject `K'_ψ`, the sections
  `s` of `X₂` whose image in `F/K'` is the image of `ψ(s̄)` in `M ⊂ F/K'`.

## Main results

* `Deformation.ToposThickening.exists_addTorsor_extensionAlong`: the principal homogeneous space
  structure, with its action.
* `Deformation.ToposThickening.extensionKernelIn_sub`: translating `d` by `ψ` takes the subobject
  cut out by `d` to its deformation by `ψ`.
* `Deformation.ToposThickening.exists_addTorsor_extensionKernelIn`: the subobjects cut out by the
  maps extending `c` form a principal homogeneous space, `φ` acting by deformation.

## References

* [Stacks Project, Tag 0CZV](https://stacks.math.columbia.edu/tag/0CZV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation.ToposThickening

section ExtensionAlong

variable {C : Type*} [Category C]

/-- The maps `d : S.X₂ ⟶ M` restricting to a prescribed `c` on `S.X₁`, for a short exact
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0`: the maps `π⁻¹(𝒦) ⟶ 𝒬 ⊗ 𝒥` extending the canonical
`I·ℱ' ⟶ 𝒬 ⊗ 𝒥` of Stacks 0CZV, each of which cuts out one lift of the quotient. -/
abbrev ExtensionAlong [Limits.HasZeroMorphisms C] (S : ShortComplex C) {M : C}
    (c : S.X₁ ⟶ M) : Type _ :=
  { d : S.X₂ ⟶ M // S.f ≫ d = c }

/-- The subobjects of `S.X₂` cut out by the maps of `ExtensionAlong S c`: those `K'` mapping
onto `S.X₃` and meeting `S.X₁` exactly in the kernel of `c`. -/
def IsExtensionKernel [Limits.HasZeroMorphisms C] (S : ShortComplex C) {M : C} (c : S.X₁ ⟶ M)
    (K' : Subobject S.X₂) : Prop :=
  Epi (K'.arrow ≫ S.g) ∧ ∀ ⦃Z : C⦄ (z : Z ⟶ S.X₁), K'.Factors (z ≫ S.f) ↔ z ≫ c = 0

variable [Abelian C]

/-- The maps extending `c` along the first map of a short exact sequence form, when there is
one, a principal homogeneous space under `Hom(S.X₃, M)`, an element `φ` sending `d` to
`d - S.g ≫ φ`. -/
theorem exists_addTorsor_extensionAlong (S : ShortComplex C) (hS : S.ShortExact) {M : C}
    (c : S.X₁ ⟶ M) (hne : Nonempty (ExtensionAlong S c)) :
    ∃ T : AddTorsor (S.X₃ ⟶ M) (ExtensionAlong S c),
      ∀ φ d, (T.vadd φ d).val = d.val - S.g ≫ φ := by
  have : Epi S.g := hS.epi_g
  obtain ⟨T, hT⟩ := addTorsor_fiber_of_exact
    (-Preadditive.leftComp M S.g)
    (Preadditive.leftComp M S.f)
    (fun a b h => (cancel_epi S.g).1 (by simpa [Preadditive.leftComp] using h))
    (fun b => by
      change S.f ≫ b = 0 ↔ ∃ a, -(S.g ≫ a) = b
      constructor
      · intro hb
        obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel b hb
        exact ⟨-a, by simpa using ha⟩
      · rintro ⟨a, rfl⟩
        simp)
    c hne
  refine ⟨T, fun φ d => ?_⟩
  refine (hT φ d).trans ?_
  change d.val + -(S.g ≫ φ) = _
  abel

variable {S : ShortComplex C} {M : C} {c : S.X₁ ⟶ M}

/-- A map extending an epimorphism is an epimorphism. -/
theorem ExtensionAlong.epi (d : ExtensionAlong S c) [Epi c] : Epi d.val := by
  have : Epi (S.f ≫ d.val) := by
    rw [d.property]
    infer_instance
  exact epi_of_epi S.f d.val

/-- The kernel of a map extending `c` maps onto `S.X₃` and meets `S.X₁` in the kernel of `c`. -/
theorem isExtensionKernel_kernelSubobject (hS : S.ShortExact) [Epi c] (d : ExtensionAlong S c) :
    IsExtensionKernel S c (kernelSubobject d.val) := by
  have := hS.epi_g
  have := d.epi
  refine ⟨Preadditive.epi_of_cancel_zero _ fun {Z} h hh => ?_, fun Z z => ?_⟩
  · obtain ⟨e, he⟩ := CokernelCofork.IsColimit.desc' (Abelian.epiIsCokernelOfKernel _
      (kernelIsKernel d.val)) (S.g ≫ h) (by
        rw [← Category.assoc]
        simpa [kernelSubobject_arrow] using
          congrArg (fun m => (kernelSubobjectIso d.val).inv ≫ m) hh)
    have he' : d.val ≫ e = S.g ≫ h := he
    have hce : c ≫ e = 0 := by
      rw [← d.property, Category.assoc, he', ← Category.assoc, S.zero, zero_comp]
    have he0 : e = 0 := (cancel_epi c).1 (by rw [hce, comp_zero])
    apply (cancel_epi S.g).1
    rw [comp_zero, ← he', he0, comp_zero]
  · rw [kernelSubobject_factors_iff, Category.assoc, d.property]

/-- Two maps extending the epimorphism `c` with the same kernel are equal. -/
theorem kernelSubobject_injective (hS : S.ShortExact) [Epi c] {d₁ d₂ : ExtensionAlong S c}
    (h : kernelSubobject d₁.val = kernelSubobject d₂.val) : d₁ = d₂ := by
  obtain ⟨hepi, -⟩ := isExtensionKernel_kernelSubobject hS d₁
  obtain ⟨φ, hφ⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel (d₁.val - d₂.val) (by
    rw [Preadditive.comp_sub, d₁.property, d₂.property, sub_self])
  change S.g ≫ φ = _ at hφ
  have h0 : ((kernelSubobject d₁.val).arrow ≫ S.g) ≫ φ = 0 := by
    rw [Category.assoc, hφ, Preadditive.comp_sub, kernelSubobject_arrow_comp]
    have := kernelSubobject_arrow_comp d₂.val
    rw [← h] at this
    rw [this, sub_zero]
  have hφ0 : φ = 0 := (cancel_epi _).1 (by rw [h0, comp_zero])
  apply Subtype.ext
  rw [← sub_eq_zero, ← hφ, hφ0, comp_zero]

/-- A map factoring through a subobject is killed by the projection to the quotient. -/
private theorem comp_cokernel_eq_zero_of_factors {A B : C} {K : Subobject B} {g : A ⟶ B}
    (hg : K.Factors g) : g ≫ cokernel.π K.arrow = 0 := by
  rw [← Subobject.factorThru_arrow _ _ hg, Category.assoc, cokernel.condition, comp_zero]

/-- A map factors through a subobject exactly when it is killed by the projection to the
quotient. -/
private theorem factors_iff_comp_cokernel_π_eq_zero {A B : C} (K : Subobject B) (g : A ⟶ B) :
    K.Factors g ↔ g ≫ cokernel.π K.arrow = 0 := by
  refine ⟨comp_cokernel_eq_zero_of_factors, fun hz => ?_⟩
  obtain ⟨w, hw⟩ := KernelFork.IsLimit.lift' (Abelian.monoIsKernelOfCokernel _
    (cokernelIsCokernel K.arrow)) g hz
  change w ≫ K.arrow = g at hw
  rw [← hw]
  exact Subobject.factors_comp_arrow w

/-- A subobject satisfying `IsExtensionKernel` is the kernel of a map extending `c`. -/
theorem exists_extensionAlong_of_isExtensionKernel (hS : S.ShortExact) [Epi c]
    {K' : Subobject S.X₂} (hK' : IsExtensionKernel S c K') :
    ∃ d : ExtensionAlong S c, kernelSubobject d.val = K' := by
  obtain ⟨hepi, hfac⟩ := hK'
  have := hS.epi_g
  let q := cokernel.π K'.arrow
  have hqK : ∀ ⦃Z : C⦄ (z : Z ⟶ S.X₂), K'.Factors z ↔ z ≫ q = 0 :=
    fun _ z => factors_iff_comp_cokernel_π_eq_zero K' z
  have hepi' : Epi (S.f ≫ q) := Preadditive.epi_of_cancel_zero _ fun {Z} h hh => by
    obtain ⟨e, he⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel (q ≫ h) (by
      rw [← Category.assoc, hh])
    change S.g ≫ e = q ≫ h at he
    have he0 : (K'.arrow ≫ S.g) ≫ e = 0 := by
      rw [Category.assoc, he, ← Category.assoc, cokernel.condition, zero_comp]
    have : e = 0 := (cancel_epi _).1 (by rw [he0, comp_zero])
    apply (cancel_epi q).1
    rw [comp_zero, ← he, this, comp_zero]
  have hker : ∀ ⦃Z : C⦄ (z : Z ⟶ S.X₁), z ≫ S.f ≫ q = 0 ↔ z ≫ c = 0 := fun Z z => by
    rw [← Category.assoc, ← hqK, hfac]
  obtain ⟨v, hv⟩ := CokernelCofork.IsColimit.desc' (Abelian.epiIsCokernelOfKernel _
      (kernelIsKernel (S.f ≫ q))) c ((hker _).1 (kernel.condition _))
  obtain ⟨u, hu⟩ := CokernelCofork.IsColimit.desc' (Abelian.epiIsCokernelOfKernel _
      (kernelIsKernel c)) (S.f ≫ q) ((hker _).2 (kernel.condition _))
  change (S.f ≫ q) ≫ v = c at hv
  change c ≫ u = S.f ≫ q at hu
  have hvu : v ≫ u = 𝟙 _ := (cancel_epi (S.f ≫ q)).1 (by
    rw [← Category.assoc, hv, hu]
    exact (Category.comp_id _).symm)
  have : Mono v := mono_of_mono_fac hvu
  refine ⟨⟨q ≫ v, by rw [← Category.assoc, hv]⟩, ?_⟩
  change kernelSubobject (q ≫ v) = K'
  rw [kernelSubobject_comp_mono]
  refine le_antisymm (Subobject.le_of_factors ?_) (Subobject.le_of_factors ?_)
  · rw [hqK, kernelSubobject_arrow_comp]
  · rw [kernelSubobject_factors_iff, ← hqK]
    exact Subobject.factors_self K'

/-- **The maps extending `c` are the subobjects they cut out.** Taking kernels is a bijection
from the maps `d : S.X₂ ⟶ M` with `S.f ≫ d = c` onto the subobjects of `S.X₂` that map onto
`S.X₃` and meet `S.X₁` in the kernel of `c`. -/
noncomputable def extensionAlongKernelEquiv (hS : S.ShortExact) [Epi c] :
    ExtensionAlong S c ≃ { K' : Subobject S.X₂ // IsExtensionKernel S c K' } :=
  Equiv.ofBijective (fun d => ⟨kernelSubobject d.val, isExtensionKernel_kernelSubobject hS d⟩)
    ⟨fun _ _ h => kernelSubobject_injective hS (congrArg Subtype.val h),
      fun K' => (exists_extensionAlong_of_isExtensionKernel hS K'.property).imp
        fun _ h => Subtype.ext h⟩

/-- `Deformation.ToposThickening.extensionAlongKernelEquiv` takes kernels. -/
theorem extensionAlongKernelEquiv_apply (hS : S.ShortExact) [Epi c] (d : ExtensionAlong S c) :
    (extensionAlongKernelEquiv hS d).val = kernelSubobject d.val := rfl

/-- In a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, a subobject `K''` of `X₂` mapping onto `X₃`
and `X₁` together cover `X₂`. -/
theorem epi_biprodDesc_of_epi_comp {S : ShortComplex C} (hS : S.ShortExact) (K'' : Subobject S.X₂)
    (hK'' : Epi (K''.arrow ≫ S.g)) : Epi (biprod.desc K''.arrow S.f) := by
  have := hS.epi_g
  refine Preadditive.epi_of_cancel_zero _ fun {Z} h hh => ?_
  have h₁ : K''.arrow ≫ h = 0 := by simpa using biprod.inl ≫= hh
  have h₂ : S.f ≫ h = 0 := by simpa using biprod.inr ≫= hh
  obtain ⟨e, he⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel h h₂
  change S.g ≫ e = h at he
  have : e = 0 := (cancel_epi (K''.arrow ≫ S.g)).1 (by
    rw [Category.assoc, he, h₁, comp_zero])
  rw [← he, this, comp_zero]

/-! ### The subobjects of an ambient object cut out by the maps extending `c` -/

section Deformation

variable [Epi c] {F : C} (j : S.X₂ ⟶ F) [Mono j]

/-- The kernel of a map `g` out of `S.X₂`, viewed as a subobject of `F` through `j`. -/
noncomputable def kernelSubobjectIn {T : C} (g : S.X₂ ⟶ T) : Subobject F :=
  Subobject.mk ((kernelSubobject g).arrow ≫ j)

/-- `kernelSubobjectIn j g` is the image under `j` of the kernel subobject of `g`. -/
theorem kernelSubobjectIn_eq_map {T : C} (g : S.X₂ ⟶ T) :
    kernelSubobjectIn j g = (Subobject.map j).obj (kernelSubobject g) := by
  rw [kernelSubobjectIn, ← Subobject.map_mk, Subobject.mk_arrow]

/-- Postcomposing `g` with a monomorphism does not change `kernelSubobjectIn j g`. -/
theorem kernelSubobjectIn_comp_mono {T T' : C} (g : S.X₂ ⟶ T) (h : T ⟶ T') [Mono h] :
    kernelSubobjectIn j (g ≫ h) = kernelSubobjectIn j g := by
  rw [kernelSubobjectIn_eq_map, kernelSubobjectIn_eq_map, kernelSubobject_comp_mono]

/-- A map into `S.X₂` lands in the kernel of `g` exactly when its composite with `j` lands in
`kernelSubobjectIn j g`. -/
theorem factors_kernelSubobjectIn_iff {T Z : C} (g : S.X₂ ⟶ T) (x : Z ⟶ S.X₂) :
    (kernelSubobjectIn j g).Factors (x ≫ j) ↔ x ≫ g = 0 := by
  rw [← kernelSubobject_factors_iff]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ : ∃ y : Z ⟶ (Subobject.mk ((kernelSubobject g).arrow ≫ j) : C),
        y ≫ (Subobject.mk ((kernelSubobject g).arrow ≫ j)).arrow = x ≫ j :=
      ⟨_, Subobject.factorThru_arrow _ _ hx⟩
    rw [← Subobject.underlyingIso_hom_comp_eq_mk ((kernelSubobject g).arrow ≫ j),
      ← Category.assoc, ← Category.assoc] at hy
    rw [← (cancel_mono j).1 hy]
    exact Subobject.factors_comp_arrow _
  · intro hx
    rw [← Subobject.factorThru_arrow _ _ hx, Category.assoc]
    exact Subobject.factors_of_factors_right _ (Subobject.mk_factors_self _)

/-- The subobject of `F` cut out by a map `d` extending `c`: the kernel of `d`, viewed in `F`
through the monomorphism `j : S.X₂ ⟶ F`. For Stacks 0CZV, `S.X₂ = π⁻¹(𝒦) ⊂ ℱ'` and this is the
lift `𝒦' ⊂ ℱ'` of `𝒦` attached to `d`. -/
noncomputable def extensionKernelIn (d : ExtensionAlong S c) : Subobject F :=
  kernelSubobjectIn j d.val

/-- The subobject cut out by `d` lies in `S.X₂` and maps onto `S.X₃`. -/
theorem exists_factor_extensionKernelIn (hS : S.ShortExact) (d : ExtensionAlong S c) :
    ∃ h : (extensionKernelIn j d : C) ⟶ S.X₂,
      h ≫ j = (extensionKernelIn j d).arrow ∧ Epi (h ≫ S.g) := by
  have := (isExtensionKernel_kernelSubobject hS d).1
  unfold extensionKernelIn kernelSubobjectIn
  refine ⟨(Subobject.underlyingIso ((kernelSubobject d.val).arrow ≫ j)).hom ≫
    (kernelSubobject d.val).arrow, ?_, ?_⟩
  · rw [Category.assoc]
    exact Subobject.underlyingIso_hom_comp_eq_mk _
  · rw [Category.assoc]
    infer_instance

/-- The quotient of `F` by the subobject cut out by `d` is the cokernel of `ker d ⟶ S.X₂ ⟶ F`. -/
noncomputable def cokernelIsoExtensionKernelIn (d : ExtensionAlong S c) :
    cokernel ((kernelSubobject d.val).arrow ≫ j) ≅ cokernel (extensionKernelIn j d).arrow :=
  (cokernelEpiComp (Subobject.underlyingIso ((kernelSubobject d.val).arrow ≫ j)).hom
    ((kernelSubobject d.val).arrow ≫ j)).symm ≪≫
    cokernelIsoOfEq (Subobject.underlyingIso_hom_comp_eq_mk _)

/-- The inclusion `M ⟶ F/K'` of the target of `c` into the quotient by a subobject `K'` of `F`
which contains the image of the kernel of `c`: the map induced by `S.X₁ ⟶ S.X₂ ⟶ F ⟶ F/K'`.
For Stacks 0CZV this is the inclusion `𝒬 ⊗ 𝒥 ⊂ 𝒬'` of the remark's diagram. -/
noncomputable def extensionInclusion (K' : Subobject F)
    (hK' : K'.Factors (kernel.ι c ≫ S.f ≫ j)) : M ⟶ cokernel K'.arrow :=
  Abelian.epiDesc c (S.f ≫ j ≫ cokernel.π K'.arrow) (by
    simpa only [Category.assoc] using comp_cokernel_eq_zero_of_factors hK')

omit [Mono j] in
/-- The map `c` followed by the inclusion `M ⟶ F/K'` is `S.X₁ ⟶ S.X₂ ⟶ F ⟶ F/K'`. -/
theorem comp_extensionInclusion (K' : Subobject F) (hK' : K'.Factors (kernel.ι c ≫ S.f ≫ j)) :
    c ≫ extensionInclusion j K' hK' = S.f ≫ j ≫ cokernel.π K'.arrow :=
  Abelian.comp_epiDesc _ _ _

/-- **The deformed subobject of the remark of Stacks 0CZV.** For a subobject `K'` of `F` and a map
`ψ : S.X₃ ⟶ M`, the subobject of the sections `s` of `S.X₂ ⊂ F` whose image in `F/K'` is the
image of `ψ(s̄)` under the inclusion `M ⊂ F/K'`, where `s̄` is the image of `s` in `S.X₃`. -/
noncomputable def extensionDeformation (K' : Subobject F)
    (hK' : K'.Factors (kernel.ι c ≫ S.f ≫ j)) (ψ : S.X₃ ⟶ M) : Subobject F :=
  kernelSubobjectIn j (j ≫ cokernel.π K'.arrow - S.g ≫ ψ ≫ extensionInclusion j K' hK')

omit [Epi c] in
/-- The subobject cut out by `d` contains the image of the kernel of `c`. -/
theorem factors_extensionKernelIn (d : ExtensionAlong S c) :
    (extensionKernelIn j d).Factors (kernel.ι c ≫ S.f ≫ j) := by
  rw [← Category.assoc, extensionKernelIn, factors_kernelSubobjectIn_iff, Category.assoc,
    d.property, kernel.condition]

/-- `d` followed by the inclusion `M ⊂ F/K'` is `S.X₂ ⟶ F ⟶ F/K'`, for the subobject `K'` cut out
by `d`. -/
theorem val_comp_extensionInclusion (hS : S.ShortExact) (d : ExtensionAlong S c) :
    d.val ≫ extensionInclusion j (extensionKernelIn j d) (factors_extensionKernelIn j d) =
      j ≫ cokernel.π (extensionKernelIn j d).arrow := by
  have hepi := epi_biprodDesc_of_epi_comp hS (kernelSubobject d.val)
    (isExtensionKernel_kernelSubobject hS d).1
  apply (cancel_epi (biprod.desc (kernelSubobject d.val).arrow S.f)).1
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, biprod.inl_desc_assoc, kernelSubobject_arrow_comp_assoc, zero_comp,
      ← Category.assoc]
    exact (comp_cokernel_eq_zero_of_factors ((factors_kernelSubobjectIn_iff j d.val _).2
      (kernelSubobject_arrow_comp d.val))).symm
  · rw [biprod.inr_desc_assoc, biprod.inr_desc_assoc, ← Category.assoc, d.property,
      comp_extensionInclusion]

/-- The inclusion `M ⊂ F/K'` is a monomorphism, for the subobject `K'` cut out by `d`. -/
theorem mono_extensionInclusion (hS : S.ShortExact) (d : ExtensionAlong S c) :
    Mono (extensionInclusion j (extensionKernelIn j d) (factors_extensionKernelIn j d)) := by
  have := d.epi
  refine (Preadditive.mono_iff_cancel_zero _).2 fun Z z hz => ?_
  obtain ⟨Z₁, p₁, hp₁, x, hx⟩ := surjective_up_to_refinements_of_epi d.val z
  have hx0 : (x ≫ j) ≫ cokernel.π (extensionKernelIn j d).arrow = 0 := by
    rw [Category.assoc, ← val_comp_extensionInclusion j hS d, ← Category.assoc, ← hx,
      Category.assoc, hz, comp_zero]
  have hfac := (factors_iff_comp_cokernel_π_eq_zero _ _).2 hx0
  rw [extensionKernelIn, factors_kernelSubobjectIn_iff] at hfac
  apply (cancel_epi p₁).1
  rw [comp_zero, hx, hfac]

/-- **The quotient by the subobject cut out by `d` contains `M`**: for `K₀` the subobject cut out
by `d`, there is a monomorphism `M ⟶ F/K₀` through which `d` and the canonical map `c` induce the
projections to `F/K₀`. -/
theorem exists_mono_extensionInclusion (hS : S.ShortExact) (d : ExtensionAlong S c)
    {K₀ : Subobject F} (hK₀ : extensionKernelIn j d = K₀) :
    ∃ ι : M ⟶ cokernel K₀.arrow, Mono ι ∧ d.val ≫ ι = j ≫ cokernel.π K₀.arrow ∧
      c ≫ ι = S.f ≫ j ≫ cokernel.π K₀.arrow := by
  subst hK₀
  exact ⟨_, mono_extensionInclusion j hS d, val_comp_extensionInclusion j hS d,
    comp_extensionInclusion j _ _⟩

/-- **The action of Stacks 0CZV on subobjects.** Translating `d` by `ψ` translates the subobject
it cuts out to the deformed subobject: the kernel of `d - (S.X₂ ⟶ S.X₃) ≫ ψ`, viewed in `F`, is the
subobject of the sections of `S.X₂` whose image in `F/K'` is the image of `ψ` of their class. -/
theorem extensionKernelIn_sub (hS : S.ShortExact) (d : ExtensionAlong S c) (ψ : S.X₃ ⟶ M) :
    kernelSubobjectIn j (d.val - S.g ≫ ψ) =
      extensionDeformation j (extensionKernelIn j d) (factors_extensionKernelIn j d) ψ := by
  have := mono_extensionInclusion j hS d
  have h : (d.val - S.g ≫ ψ) ≫
      extensionInclusion j (extensionKernelIn j d) (factors_extensionKernelIn j d) =
      j ≫ cokernel.π (extensionKernelIn j d).arrow -
        S.g ≫ ψ ≫ extensionInclusion j (extensionKernelIn j d) (factors_extensionKernelIn j d) := by
    rw [Preadditive.sub_comp, val_comp_extensionInclusion j hS d, Category.assoc]
  rw [extensionDeformation, ← h, kernelSubobjectIn_comp_mono]

/-- Distinct maps extending `c` cut out distinct subobjects of `F`: `extensionKernelIn j` is
injective. -/
theorem extensionKernelIn_injective (hS : S.ShortExact) :
    Function.Injective (extensionKernelIn j : ExtensionAlong S c → Subobject F) := by
  intro d₁ d₂ h
  rw [extensionKernelIn, extensionKernelIn, kernelSubobjectIn_eq_map,
    kernelSubobjectIn_eq_map] at h
  exact kernelSubobject_injective hS (Subobject.map_obj_injective j h)

/-- **The principal homogeneous space of lifts, with the action of Stacks 0CZV.** Let `Lift` be a
property of subobjects of `F` satisfied exactly by the subobjects cut out by the maps extending
`c`. If some subobject has it, the subobjects having it form a principal homogeneous space under
any group `G` identified with `Hom(S.X₃, M)` by `g`, an element `φ` sending `K'` to the deformed
subobject `extensionDeformation j K' _ (g φ)` of the remark. -/
@[sga "3 III 4.1" "Lemma 4.1 (ii)"]
theorem exists_addTorsor_extensionKernelIn (hS : S.ShortExact) {G : Type*} [AddGroup G]
    (g : G ≃+ (S.X₃ ⟶ M)) (Lift : Subobject F → Prop)
    (h₁ : ∀ d : ExtensionAlong S c, Lift (extensionKernelIn j d))
    (h₂ : ∀ K', Lift K' → ∃ d : ExtensionAlong S c, extensionKernelIn j d = K')
    (hne : Nonempty {K' // Lift K'}) :
    ∃ T : AddTorsor G {K' // Lift K'},
      ∀ (φ : G) (K' : {K' // Lift K'}) (hK : K'.val.Factors (kernel.ι c ≫ S.f ≫ j)),
        (T.vadd φ K').val = extensionDeformation j K'.val hK (g φ) := by
  let E : ExtensionAlong S c ≃ {K' // Lift K'} :=
    Equiv.ofBijective (fun d => ⟨extensionKernelIn j d, h₁ d⟩)
      ⟨fun _ _ h => extensionKernelIn_injective j hS (congrArg Subtype.val h),
        fun K' => (h₂ K'.val K'.property).imp fun _ h => Subtype.ext h⟩
  obtain ⟨d₀, -⟩ := h₂ _ hne.some.property
  obtain ⟨T₀, hT₀⟩ := exists_addTorsor_extensionAlong S hS c ⟨d₀⟩
  let := T₀
  refine ⟨addTorsorCongr g E.symm, fun φ K' hK => ?_⟩
  obtain ⟨K', hK'⟩ := K'
  obtain ⟨d, rfl⟩ := h₂ K' hK'
  have hd : E.symm ⟨extensionKernelIn j d, hK'⟩ = d :=
    E.symm_apply_eq.2 rfl
  change (E (g φ +ᵥ E.symm ⟨extensionKernelIn j d, hK'⟩)).val = _
  rw [hd]
  change extensionKernelIn j (g φ +ᵥ d) = _
  rw [extensionKernelIn, show (g φ +ᵥ d).val = d.val - S.g ≫ g φ from hT₀ (g φ) d]
  exact extensionKernelIn_sub j hS d (g φ)

end Deformation

end ExtensionAlong

end Deformation.ToposThickening

end
