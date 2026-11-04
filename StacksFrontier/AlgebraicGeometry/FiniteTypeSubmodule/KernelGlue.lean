module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.AffineCase
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.Locality
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# The two-chart case of the finite type extension lemma

-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.FiniteTypeSubmodule

/-! ### Two generalities about kernels and cokernels -/

section Generalities

variable {C : Type*} [Category C] [Limits.HasZeroMorphisms C]

/-- The kernel inclusion of a morphism which is zero is an isomorphism. -/
theorem isIso_kernel_ι_of_eq_zero {A B : C} (g : A ⟶ B) [HasKernel g] (hg : g = 0) :
    IsIso (kernel.ι g) := by
  refine ⟨kernel.lift g (𝟙 A) (by simp [hg]), ?_, kernel.lift_ι _ _ _⟩
  rw [← cancel_mono (kernel.ι g), Category.assoc, kernel.lift_ι, Category.comp_id,
    Category.id_comp]

/-- The cokernel of an epimorphism is a zero object. -/
theorem isZero_cokernel_of_epi [HasZeroObject C] {A B : C} (g : A ⟶ B) [Epi g] [HasCokernel g] :
    IsZero (cokernel g) := by
  have hπ : cokernel.π g = 0 := by
    rw [← cancel_epi g, cokernel.condition, comp_zero]
  have hid : 𝟙 (cokernel g) = 0 := by
    rw [← cancel_epi (cokernel.π g), Category.comp_id, hπ, comp_zero]
  exact IsZero.of_iso (isZero_zero C) ((idZeroEquivIsoZero _) hid)

end Generalities

/-! ### Sections of a module which vanishes on an open -/

/-- The sections of a zero module over any open vanish. -/
theorem subsingleton_sections_of_isZero {X : Scheme.{u}} {M : X.Modules} (h : IsZero M)
    (U : X.Opens) : Subsingleton Γ(M, U) := by
  have hid : Scheme.Modules.Hom.app (𝟙 M) U = Scheme.Modules.Hom.app (0 : M ⟶ M) U :=
    congrArg (fun φ : M ⟶ M => Scheme.Modules.Hom.app φ U) (h.eq_zero_of_tgt (𝟙 M))
  have hzero : ∀ z : Γ(M, U), z = 0 := by
    intro z
    simpa using congrArg (fun k : Γ(M, U) ⟶ Γ(M, U) => k.hom z) hid
  exact ⟨fun x y => by rw [hzero x, hzero y]⟩

/-- If a module becomes zero after restriction to an open `U`, then its sections over every open
contained in `U` vanish. -/
theorem subsingleton_sections_of_isZero_restrict {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    (h : IsZero (M.restrict U.ι)) {O : X.Opens} (hO : O ≤ U) : Subsingleton Γ(M, O) := by
  have hopen : U.ι ''ᵁ (U.ι ⁻¹ᵁ O) = O := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hO
  rw [← hopen]
  exact subsingleton_sections_of_isZero h (U.ι ⁻¹ᵁ O)

/-- A morphism of sheaves of modules whose target has no nonzero sections is zero. -/
theorem eq_zero_of_subsingleton_sections {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U : X.Opens, Subsingleton Γ(N, U)) : φ = 0 :=
  Scheme.Modules.hom_ext _ _ fun U => by
    have := h U
    ext x
    exact Subsingleton.elim _ _

/-! ### The two-chart case -/

variable {X : Scheme.{u}}

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory in
/-- **The two-chart case of [Stacks Project, Tag 01PF].** Let `X` be a scheme covered by two
opens `W` and `V` with `V` affine, and let `H` be a quasi-coherent module which is of finite
type on `W`. Then `H` has a quasi-coherent submodule of finite type whose inclusion restricts to
an isomorphism over `W`.

This is the second paragraph of the source's proof, in the only case the induction needs. The
submodule is the kernel of
`H ⟶ (V.ι)_* ((H|_V) / C)`,
where `C ⊆ H|_V` is the submodule produced by the affine case on `V` for the quasi-compact open
`W ⊓ V`, and the map is the unit of `restrict ⊣ pushforward` followed by the quotient. Over `V`
the kernel is `C`, because restriction is exact, the counit of the adjunction is an isomorphism
and a monomorphism in an abelian category is the kernel of its cokernel. Over `W` the kernel is
all of `H`, because `C → H|_V` is an isomorphism over `W ⊓ V`, so the quotient vanishes there,
so the pushforward has no nonzero sections over any open of `W`, so the map is zero on `W`.

No gluing of subobjects is needed: one of the two charts carries all of `H`, so the glued
subobject is a single preimage rather than an intersection of two. -/
theorem exists_isFiniteType_submodule_isIso_restrict_sup (H : X.Modules)
    [H.IsQuasicoherent] (W V : X.Opens) (hV : IsAffineOpen V) [QuasiCompact V.ι]
    (hcomp : IsCompact ((W ⊓ V : X.Opens) : Set X))
    (hft : (H.restrict W.ι).IsFiniteType) :
    ∃ (A : X.Modules) (ι : A ⟶ H), A.IsQuasicoherent ∧
      SheafOfModules.IsFiniteType.{u, u, u} (A.restrict (W ⊔ V).ι) ∧ Mono ι ∧
      IsIso ((Scheme.Modules.restrictFunctor W.ι).map ι) := by
  classical
  let _ : IsAffine V.toScheme := hV
  set V' : V.toScheme.Opens := V.ι ⁻¹ᵁ W with hV'def
  have hftV : ((H.restrict V.ι).restrict V'.ι).IsFiniteType :=
    isFiniteType_restrict_restrict_of_le H V W hft
  obtain ⟨C, hCqc, hCft, hCiso⟩ :=
    exists_finiteTypeQuasicoherentSubobject_isIso_restrict (H.restrict V.ι)
      (isCompact_preimage_ι V W hcomp) hftV
  -- the morphism whose kernel is the submodule
  let L := Scheme.Modules.restrictFunctor V.ι
  let R := Scheme.Modules.pushforward V.ι
  let adj := Scheme.Modules.restrictAdjunction V.ι
  let q : H ⟶ R.obj (cokernel C.arrow) := adj.unit.app H ≫ R.map (cokernel.π C.arrow)
  let ι₀ : kernel q ⟶ H := kernel.ι q
  -- over `V` the kernel is `C`
  have hq' : L.map q ≫ adj.counit.app (cokernel C.arrow) = cokernel.π C.arrow := by
    simp only [Functor.id_obj, Functor.comp_obj, Functor.map_comp, Category.assoc,
      Adjunction.counit_naturality, Adjunction.left_triangle_components_assoc, L, q]
  have hC : IsLimit (KernelFork.ofι (f := cokernel.π C.arrow) C.arrow
      (cokernel.condition C.arrow)) :=
    Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)
  have e3 : kernel (cokernel.π C.arrow) ≅ (C : V.toScheme.Modules) :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel (cokernel.π C.arrow)) hC
  have eV : L.obj (kernel q) ≅ (C : V.toScheme.Modules) :=
    asIso (kernelComparison q L) ≪≫
      (kernelCompMono (L.map q) (adj.counit.app (cokernel C.arrow))).symm ≪≫
      kernelIsoOfEq hq' ≪≫ e3
  -- over `W` the kernel is all of `H`
  have hKzero : IsZero ((cokernel C.arrow).restrict V'.ι) := by
    have hiso : IsIso ((Scheme.Modules.restrictFunctor V'.ι).map C.arrow) := hCiso
    exact IsZero.of_iso
      (isZero_cokernel_of_epi ((Scheme.Modules.restrictFunctor V'.ι).map C.arrow))
      (asIso (cokernelComparison C.arrow (Scheme.Modules.restrictFunctor V'.ι))).symm
  have hqW : (Scheme.Modules.restrictFunctor W.ι).map q = 0 := by
    refine eq_zero_of_subsingleton_sections _ fun O => ?_
    have hle : (V.ι ⁻¹ᵁ (W.ι ''ᵁ O) : V.toScheme.Opens) ≤ V' :=
      fun x hx => Scheme.Opens.ι_image_le W O hx
    exact subsingleton_sections_of_isZero_restrict hKzero hle
  have hisoW : IsIso ((Scheme.Modules.restrictFunctor W.ι).map ι₀) := by
    rw [show (Scheme.Modules.restrictFunctor W.ι).map ι₀ =
        kernelComparison q (Scheme.Modules.restrictFunctor W.ι) ≫
          kernel.ι ((Scheme.Modules.restrictFunctor W.ι).map q) from
      (kernelComparison_comp_ι q _).symm]
    have : IsIso (kernel.ι ((Scheme.Modules.restrictFunctor W.ι).map q)) :=
      isIso_kernel_ι_of_eq_zero _ hqW
    infer_instance
  -- quasi-coherence is [Stacks Project, Tag 01LC]; finite type is local on the two charts
  have hWiso : (Scheme.Modules.restrictFunctor W.ι).obj (kernel q) ≅
      (Scheme.Modules.restrictFunctor W.ι).obj H :=
    have := hisoW
    asIso ((Scheme.Modules.restrictFunctor W.ι).map ι₀)
  have hA₀qc : (kernel q).IsQuasicoherent := by
    have h2 : (C : V.toScheme.Modules).IsQuasicoherent := hCqc
    have h3 : (cokernel C.arrow).IsQuasicoherent := inferInstance
    have h4 : ((Scheme.Modules.pushforward V.ι).obj (cokernel C.arrow)).IsQuasicoherent :=
      inferInstance
    exact Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel q
  have hWft : ((kernel q).restrict W.ι).IsFiniteType := by
    have := hft
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} hWiso.symm
  have hVft : ((kernel q).restrict V.ι).IsFiniteType := by
    have := hCft
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} eV.symm
  have hA₀ft : SheafOfModules.IsFiniteType.{u, u, u} ((kernel q).restrict (W ⊔ V).ι) :=
    have := hA₀qc
    isFiniteType_restrict_sup (kernel q) W V hWft hVft
  exact ⟨kernel q, ι₀, hA₀qc, hA₀ft, inferInstance, hisoW⟩

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory in
/-- **The one-extra-affine step of [Stacks Project, Tag 01PF], as a subobject.** The same
statement as `exists_isFiniteType_submodule_isIso_restrict_sup` in the same namespace, with the
submodule presented as a `CategoryTheory.Subobject`. -/
theorem exists_subobject_isFiniteType_isIso_restrict_sup (H : X.Modules)
    [H.IsQuasicoherent] (W V : X.Opens) (hV : IsAffineOpen V) [QuasiCompact V.ι]
    (hcomp : IsCompact ((W ⊓ V : X.Opens) : Set X))
    (hft : (H.restrict W.ι).IsFiniteType) :
    ∃ A : Subobject H, (A : X.Modules).IsQuasicoherent ∧
      SheafOfModules.IsFiniteType.{u, u, u} ((A : X.Modules).restrict (W ⊔ V).ι) ∧
      IsIso ((Scheme.Modules.restrictFunctor W.ι).map A.arrow) := by
  obtain ⟨A₀, ι, hqc, hftA, hmono, hiso⟩ :=
    exists_isFiniteType_submodule_isIso_restrict_sup H W V hV hcomp hft
  have := hmono
  refine ⟨Subobject.mk ι, ?_, ?_, ?_⟩
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso ι).symm hqc
  · have : SheafOfModules.IsFiniteType.{u, u, u} (A₀.restrict (W ⊔ V).ι) := hftA
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Scheme.Modules.restrictFunctor (W ⊔ V).ι).mapIso (Subobject.underlyingIso ι).symm)
  · have harrow : (Subobject.mk ι).arrow = (Subobject.underlyingIso ι).hom ≫ ι := by
      rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    rw [harrow, Functor.map_comp]
    have := hiso
    infer_instance

end Stacks.AlgebraicGeometry.FiniteTypeSubmodule

end
