module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Full subcategories whose kernels are coreflected from an ambient subcategory

Let `𝒜` be an abelian category and `C ≤ P` two properties of objects of `𝒜`.  Suppose `C` is
closed under the cokernels of `𝒜`, but not necessarily under its kernels: instead, for every map
`f` between objects of `C` there is an object `K` of `C` with a map `k : K ⟶ X` which is a kernel
of `f` *relative to `P`*, i.e. every map from an object of `P` killed by `f` factors uniquely
through `k`.  Suppose finally that there is an exact functor `L : 𝒜 ⥤ 𝒜'` to an abelian category
which reflects isomorphisms between objects of `P` and carries each such `k` to a kernel of
`L f`.

Then the full subcategory cut out by `C` is abelian, its kernels are the relative kernels `k`,
its cokernels are those of `𝒜`, and the inclusion of `C` into `P` preserves kernels and cokernels.

This is the shape of Stacks 0GR9: `𝒜` is `Mod(𝒪_𝒳)`, `P` the quasi-coherent and `C` the coherent
modules, `k` is `Q(Ker φ) ⟶ 𝓕`, and `L` is restriction to the flat-fppf site, which sees
`Q(Ker φ)` and `Ker φ` as equal (the kernel and cokernel of `Q(Ker φ) ⟶ Ker φ` are parasitic,
Stacks 0779) and reflects isomorphisms between quasi-coherent modules.

## Main definitions

* `CategoryTheory.ObjectProperty.IsRelKernel`: `k` is a kernel of `f` relative to `P`.
* `CategoryTheory.ObjectProperty.RelKernelData`: the hypotheses on `P`, `C` and `L` above.

## Main results

* `CategoryTheory.ObjectProperty.RelKernelData.isIso_coimageImageComparison` and
  `CategoryTheory.ObjectProperty.RelKernelData.nonempty_abelian`: the full subcategory is
  abelian.
* `CategoryTheory.ObjectProperty.RelKernelData.preservesKernel_ιOfLE` and
  `CategoryTheory.ObjectProperty.RelKernelData.preservesCokernel_ιOfLE`: the inclusion into `P`
  preserves kernels and cokernels.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

universe v v' u u'

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- `k : K ⟶ X` is a kernel of `f : X ⟶ Y` *relative to `P`*: `k ≫ f = 0`, and every map out of
an object satisfying `P` that is killed by `f` factors uniquely through `k`.  When `K` itself
satisfies `P` this says exactly that `k` is a kernel of `f` in the full subcategory of `P`. -/
def IsRelKernel (P : ObjectProperty 𝒜) {X Y K : 𝒜} (f : X ⟶ Y) (k : K ⟶ X) : Prop :=
  k ≫ f = 0 ∧ ∀ Z : 𝒜, P Z → ∀ g : Z ⟶ X, g ≫ f = 0 → ∃! t : Z ⟶ K, t ≫ k = g

namespace IsRelKernel

variable {P : ObjectProperty 𝒜} {X Y K : 𝒜} {f : X ⟶ Y} {k : K ⟶ X}

/-- A relative kernel lying in a property `C ≤ P` is a kernel in the full subcategory of `C`. -/
noncomputable def isLimitFullSubcategory {C : ObjectProperty 𝒜} (hCP : C ≤ P)
    (h : IsRelKernel P f k) (hX : C X) (hY : C Y) (hK : C K) :
    IsLimit (KernelFork.ofι (f := (C.homMk f : (⟨X, hX⟩ : C.FullSubcategory) ⟶ ⟨Y, hY⟩))
      (C.homMk k : (⟨K, hK⟩ : C.FullSubcategory) ⟶ ⟨X, hX⟩)
      (by ext; exact h.1)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {Z} g hg => C.homMk (h.2 Z.obj (hCP _ Z.property) g.hom
      (by simpa using congrArg InducedCategory.Hom.hom hg)).exists.choose)
    (fun {Z} g hg => by
      ext
      exact (h.2 Z.obj (hCP _ Z.property) g.hom
        (by simpa using congrArg InducedCategory.Hom.hom hg)).exists.choose_spec)
    (fun {Z} g hg m hm => by
      ext
      exact (h.2 Z.obj (hCP _ Z.property) g.hom
        (by simpa using congrArg InducedCategory.Hom.hom hg)).unique
        (by simpa using congrArg InducedCategory.Hom.hom hm)
        (h.2 Z.obj (hCP _ Z.property) g.hom
          (by simpa using congrArg InducedCategory.Hom.hom hg)).exists.choose_spec)

end IsRelKernel

variable {𝒜' : Type u'} [Category.{v'} 𝒜'] [Abelian 𝒜']

section

variable (P C : ObjectProperty 𝒜) (L : 𝒜 ⥤ 𝒜') [L.PreservesZeroMorphisms]

/-- The conditions on `P`, `C` and `L`: `C ≤ P`, `C` is closed under isomorphisms, contains a
zero object, is closed under finite products and under the cokernels of `𝒜`, has relative kernels
in `C` carried by `L` to kernels, and `L` is exact and reflects isomorphisms between objects of
`P`. -/
structure RelKernelData : Prop where
  /-- `C` is contained in `P`. -/
  le : C ≤ P
  /-- `C` is closed under isomorphisms. -/
  isClosedUnderIsomorphisms : C.IsClosedUnderIsomorphisms
  /-- `C` contains a zero object. -/
  containsZero : C.ContainsZero
  /-- `C` is closed under finite products. -/
  isClosedUnderFiniteProducts : C.IsClosedUnderFiniteProducts
  /-- The cokernel in `𝒜` of a map between objects of `C` lies in `C`. -/
  prop_cokernel : ∀ {X Y : 𝒜} (f : X ⟶ Y), C X → C Y → C (cokernel f)
  /-- Every map `f` between objects of `C` has a kernel `k` relative to `P` with source in `C`,
  and `L.map k` is a kernel of `L.map f`. -/
  exists_relKernel : ∀ {X Y : 𝒜} (f : X ⟶ Y), C X → C Y →
    ∃ (K : 𝒜) (k : K ⟶ X) (h : IsRelKernel P f k), C K ∧
      Nonempty (IsLimit (KernelFork.ofι (L.map k)
        (show L.map k ≫ L.map f = 0 by rw [← L.map_comp, h.1, L.map_zero])))
  /-- `L` preserves finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits L
  /-- `L` preserves finite colimits. -/
  preservesFiniteColimits : PreservesFiniteColimits L
  /-- `L` reflects isomorphisms between objects of `P`. -/
  reflects : ∀ {X Y : 𝒜} (g : X ⟶ Y), P X → P Y → IsIso (L.map g) → IsIso g

end

variable {P C : ObjectProperty 𝒜} {L : 𝒜 ⥤ 𝒜'} [L.PreservesZeroMorphisms]

/-- A functor preserves the kernel of `f` if it carries a kernel fork of `f` to a limit fork. -/
private theorem preservesLimit_of_isLimit_kerι {E D : Type*} [Category E] [Category D]
    [HasZeroMorphisms E] [HasZeroMorphisms D] {F : E ⥤ D} [F.PreservesZeroMorphisms]
    {X Y K : E} {f : X ⟶ Y} {k : K ⟶ X} {hk : k ≫ f = 0}
    (hl : IsLimit (KernelFork.ofι k hk)) (hF : IsLimit (KernelFork.ofι (F.map k)
      (by rw [← F.map_comp, hk, F.map_zero]))) :
    PreservesLimit (parallelPair f 0) F :=
  preservesLimit_of_preserves_limit_cone hl ((KernelFork.isLimitMapConeEquiv _ _).symm hF)

namespace RelKernelData

variable (hd : RelKernelData P C L)
include hd

/-- The chosen relative kernel of a map of `C`, as an object of `C`. -/
noncomputable def kerObj {X Y : C.FullSubcategory} (f : X ⟶ Y) : C.FullSubcategory :=
  ⟨(hd.exists_relKernel f.hom X.2 Y.2).choose,
    (hd.exists_relKernel f.hom X.2 Y.2).choose_spec.choose_spec.choose_spec.1⟩

/-- The chosen relative kernel map. -/
noncomputable def kerι {X Y : C.FullSubcategory} (f : X ⟶ Y) : hd.kerObj f ⟶ X :=
  C.homMk (hd.exists_relKernel f.hom X.2 Y.2).choose_spec.choose

/-- The chosen relative kernel map is a kernel of `f` relative to `P`. -/
lemma isRelKernel_kerι {X Y : C.FullSubcategory} (f : X ⟶ Y) :
    IsRelKernel P f.hom (hd.kerι f).hom :=
  (hd.exists_relKernel f.hom X.2 Y.2).choose_spec.choose_spec.choose

/-- The chosen relative kernel map composed with `f` is zero. -/
lemma kerι_comp {X Y : C.FullSubcategory} (f : X ⟶ Y) : hd.kerι f ≫ f = 0 := by
  ext; exact (hd.isRelKernel_kerι f).1

/-- The chosen relative kernel is a kernel in the full subcategory of `C`. -/
noncomputable def isLimitKer {X Y : C.FullSubcategory} (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι (hd.kerι f) (hd.kerι_comp f)) :=
  (hd.isRelKernel_kerι f).isLimitFullSubcategory (f := f.hom) hd.le X.2 Y.2 (hd.kerObj f).2

/-- `L` carries the chosen relative kernel to a kernel. -/
noncomputable def isLimitMapKer {X Y : C.FullSubcategory} (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι (L.map (hd.kerι f).hom)
      (show L.map (hd.kerι f).hom ≫ L.map f.hom = 0 by
        rw [← L.map_comp, (hd.isRelKernel_kerι f).1, L.map_zero])) :=
  (hd.exists_relKernel f.hom X.2 Y.2).choose_spec.choose_spec.choose_spec.2.some

/-- The full subcategory of `C` has kernels. -/
lemma hasKernels : HasKernels C.FullSubcategory :=
  ⟨fun f => ⟨⟨⟨_, hd.isLimitKer f⟩⟩⟩⟩

/-- `C` is closed under the cokernels of `𝒜`. -/
lemma isClosedUnderCokernels : C.IsClosedUnderCokernels where
  cokernels_le := by
    have := hd.isClosedUnderIsomorphisms
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact C.prop_of_iso (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
      (hd.prop_cokernel f hX hY)

/-- The composite `C ⥤ 𝒜 ⥤ 𝒜'` preserves kernels. -/
lemma preservesKernel_ι_comp {X Y : C.FullSubcategory} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) (C.ι ⋙ L) :=
  preservesLimit_of_isLimit_kerι (hd.isLimitKer f)
    (IsLimit.ofIsoLimit (hd.isLimitMapKer f)
      (Fork.ext (Iso.refl _) (by simp)))

/-- The composite `C ⥤ 𝒜 ⥤ 𝒜'` preserves cokernels. -/
lemma preservesCokernel_ι_comp {X Y : C.FullSubcategory} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) (C.ι ⋙ L) := by
  have := hd.isClosedUnderCokernels
  have := C.preservesCokernels_ι f
  have := hd.preservesFiniteColimits
  infer_instance

/-- **The coimage–image comparison of a map of `C` is an isomorphism.** -/
theorem isIso_coimageImageComparison [HasCokernels C.FullSubcategory]
    {X Y : C.FullSubcategory} (f : X ⟶ Y) :
    letI := hd.hasKernels
    IsIso (Abelian.coimageImageComparison f) := by
  let := hd.hasKernels
  set F := C.ι ⋙ L
  have := hd.preservesKernel_ι_comp f
  have := hd.preservesKernel_ι_comp (cokernel.π f)
  have := hd.preservesCokernel_ι_comp f
  have := hd.preservesCokernel_ι_comp (kernel.ι f)
  let e₁ : Abelian.coimage (F.map f) ≅ F.obj (Abelian.coimage f) :=
    (cokernel.mapIso (F.map (kernel.ι f)) (kernel.ι (F.map f))
      (PreservesKernel.iso F f) (Iso.refl _) (by simp)).symm.trans
      (PreservesCokernel.iso F (kernel.ι f)).symm
  let e₂ : F.obj (Abelian.image f) ≅ Abelian.image (F.map f) :=
    (PreservesKernel.iso F (cokernel.π f)).trans
      (kernel.mapIso (F.map (cokernel.π f)) (cokernel.π (F.map f)) (Iso.refl _)
        (PreservesCokernel.iso F f) (by simp))
  have h₁ : Abelian.coimage.π (F.map f) ≫ e₁.hom = F.map (Abelian.coimage.π f) := by
    simp [e₁, Abelian.coimage.π]
  have h₂ : e₂.hom ≫ Abelian.image.ι (F.map f) = F.map (Abelian.image.ι f) := by
    simp [e₂, Abelian.image.ι]
  have key : e₁.hom ≫ F.map (Abelian.coimageImageComparison f) ≫ e₂.hom =
      Abelian.coimageImageComparison (F.map f) := by
    rw [← cancel_epi (Abelian.coimage.π (F.map f)), ← cancel_mono (Abelian.image.ι (F.map f))]
    simp only [Category.assoc, h₂, reassoc_of% h₁]
    rw [← F.map_comp, ← F.map_comp, Abelian.coimage_image_factorisation,
      Abelian.coimage_image_factorisation]
  have hF : IsIso (F.map (Abelian.coimageImageComparison f)) := by
    have : IsIso (e₁.hom ≫ F.map (Abelian.coimageImageComparison f) ≫ e₂.hom) := by
      rw [key]; infer_instance
    have : IsIso (F.map (Abelian.coimageImageComparison f) ≫ e₂.hom) :=
      IsIso.of_isIso_comp_left e₁.hom _
    exact IsIso.of_isIso_comp_right _ e₂.hom
  rw [← C.isIso_hom_iff]
  exact hd.reflects _ (hd.le _ (Abelian.coimage f).2) (hd.le _ (Abelian.image f).2) hF

/-- **The full subcategory of `C` is abelian.** -/
theorem nonempty_abelian : Nonempty (Abelian C.FullSubcategory) := by
  let := hd.hasKernels
  have := hd.isClosedUnderCokernels
  have := hd.isClosedUnderFiniteProducts
  have := fun {X Y : C.FullSubcategory} (f : X ⟶ Y) => hd.isIso_coimageImageComparison f
  exact ⟨Abelian.ofCoimageImageComparisonIsIso⟩

/-- **The inclusion of `C` into `P` preserves kernels**: the kernel of a map of `C` in `C` is its
relative kernel, which is a kernel in `P`. -/
lemma preservesKernel_ιOfLE {X Y : C.FullSubcategory} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) (ιOfLE hd.le) :=
  preservesLimit_of_isLimit_kerι (hd.isLimitKer f) <|
    IsLimit.ofIsoLimit
      ((hd.isRelKernel_kerι f).isLimitFullSubcategory (C := P) (f := f.hom) le_rfl
        (hd.le _ X.2) (hd.le _ Y.2) (hd.le _ (hd.kerObj f).2))
      (Fork.ext (Iso.refl _) (by ext; simp))

/-- **The inclusion of `C` into `P` preserves cokernels**: the cokernel of a map of `C` in `C` is
its cokernel in `𝒜`, which lies in `C` and hence in `P`. -/
lemma preservesCokernel_ιOfLE {X Y : C.FullSubcategory} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) (ιOfLE hd.le) := by
  have := hd.isClosedUnderCokernels
  have := C.preservesCokernels_ι f
  have : PreservesColimit (parallelPair f 0) (ιOfLE hd.le ⋙ P.ι) :=
    inferInstanceAs (PreservesColimit (parallelPair f 0) C.ι)
  exact preservesColimit_of_reflects_of_preserves (ιOfLE hd.le) P.ι

end RelKernelData

end CategoryTheory.ObjectProperty

end
