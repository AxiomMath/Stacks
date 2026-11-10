module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafGeneratedIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafLiftSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsDirected
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSectionsConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover

/-!
# A finite quasi-coherent algebra as a quotient system of a symmetric algebra

Let `Y` be a quasi-compact and quasi-separated algebraic space and `𝒜` a finite quasi-coherent
`𝒪_Y`-algebra, and let `p : 𝒢 ⟶ 𝒜` be an epimorphism of `𝒪_Y`-modules out of a quasi-coherent
module of finite presentation.  This file carries out the proof of Stacks 086Z from that point:

* `ℬ = Sym(𝒢)` is a quasi-coherent `𝒪_Y`-algebra of finite presentation and `p` induces a locally
  surjective morphism of algebras `ℬ ⟶ 𝒜`
  (`AlgebraicGeometry.Space.isQuasicoherent_symmetricAlgebraSheaf`,
  `AlgebraicGeometry.Space.isFinitePresentation_symmetricAlgebraSheaf`,
  `AlgebraicGeometry.Space.isLocallySurjective_algebraLift`);
* the kernel `𝒦` of `ℬ ⟶ 𝒜` is a quasi-coherent `𝒪_Y`-module, and its finite type
  quasi-coherent submodules `ℰ` form a filtered system;
* the quotients `ℬ/(ℰ)` by the sheaves of ideals they generate are quasi-coherent of finite
  presentation (`StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafGeneratedIdeal`), and
  their cocone over `𝒜` is colimiting, because every local section of `𝒦` over an affine chart lies
  in one `ℰ` — the étale extension property behind Stacks 0829,
  `AlgebraicGeometry.Space.chartExtensionProperty_id`;
* for one `ℰ` the quotient `ℬ/(ℰ)` is finite: over an affine étale chart covering `Y`, the
  generators of `𝒢` satisfy monic equations in `𝒜`, which are sections of `𝒦` lying in one `ℰ`.

The resulting data are exactly what
`AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective` turns
into the directed system of Stacks 086Z.

## Main results

* `Stacks.SymAlg.isIntegral_of_surjective`: an algebra which is a quotient of a symmetric algebra
  is integral as soon as the images of a spanning family of degree-one generators are.
* `AlgebraicGeometry.Space.exists_idealQuotient_system_of_epi`: the data of the source's proof of
  Stacks 086Z, from a finitely presented module surjecting onto the algebra.
* `AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective_of_epi`:
  the conclusion of Stacks 086Z from such a module.

## References

* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SymAlg

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {C : Type*} [CommRing C] [Algebra R C]

/-- **A quotient of a symmetric algebra is integral as soon as the images of a spanning family of
degree-one generators are integral.**  The integral elements form a subalgebra, which contains the
image of every degree-one generator because the image of `ι` is linear in the generator. -/
theorem isIntegral_of_surjective (χ : SymmetricAlgebra R M →ₐ[R] C)
    (hχ : Function.Surjective χ) (t : Set M) (ht : Submodule.span R t = ⊤)
    (hint : ∀ e ∈ t, IsIntegral R (χ (SymmetricAlgebra.ι R M e))) : Algebra.IsIntegral R C := by
  refine ⟨fun c => ?_⟩
  obtain ⟨s, rfl⟩ := hχ c
  have hι : ∀ m : M, IsIntegral R (χ (SymmetricAlgebra.ι R M m)) := by
    intro m
    have hm : m ∈ Submodule.span R t := ht ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx => exact hint x hx
    | zero => rw [map_zero, map_zero]; exact isIntegral_zero
    | add x y _ _ hx hy => simpa only [map_add] using hx.add hy
    | smul r x _ hx => simpa only [map_smul] using hx.smul r
  induction s using SymmetricAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact isIntegral_algebraMap
  | ι m => exact hι m
  | mul x y hx hy => simpa only [map_mul] using hx.mul hy
  | add x y hx hy => simpa only [map_add] using hx.add hy

end Stacks.SymAlg

namespace AlgebraicGeometry.Space

open AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Y : AlgebraicSpaces B S hS}

/-! ### The kernel of `Sym(𝒢) ⟶ 𝒜` and the sheaves of ideals generated by its submodules -/

section KernelIdeals

variable {ℬ C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2} (f : ℬ ⟶ C)

/-- The `𝒪_Y`-module kernel of a morphism of algebra sheaves. -/
noncomputable abbrev algebraKernel : Modules.{u, u} B S hS Y.1 Y.2 :=
  kernel (underlyingModuleMap f)

/-- A finite type quasi-coherent submodule of the kernel, as a morphism into the underlying module
of the source. -/
noncomputable abbrev kernelSubmoduleMap
    (E : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f)) :
    (E.obj : Modules.{u, u} B S hS Y.1 Y.2) ⟶ underlyingModule ℬ :=
  E.obj.arrow ≫ kernel.ι (underlyingModuleMap f)

/-- The sheaf of ideals of `ℬ` generated by a finite type quasi-coherent submodule of the kernel
of `f : ℬ ⟶ 𝒞`. -/
noncomputable abbrev kernelSubmoduleIdeal
    (E : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f)) : ℬ.IdealSheaf :=
  generatedIdeal ℬ (kernelSubmoduleMap f E)

/-- The sheaves of ideals generated by the submodules of the kernel grow with the submodules. -/
theorem kernelSubmoduleIdeal_mono
    {E E' : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f)} (h : E ⟶ E') :
    kernelSubmoduleIdeal f E ≤ kernelSubmoduleIdeal f E' := by
  refine generatedIdeal_mono ℬ _ _ fun V e => ?_
  refine ⟨(Subobject.ofLE _ _ (leOfHom h.hom)).val.app V e, ?_⟩
  change ((Subobject.ofLE _ _ (leOfHom h.hom) ≫ E'.obj.arrow) ≫
    kernel.ι (underlyingModuleMap f)).val.app V e = _
  rw [Subobject.ofLE_arrow]

/-- **The sheaves of ideals generated by the submodules of the kernel are killed by `f`.** -/
theorem kernelSubmoduleIdeal_le_kerIdeal
    (E : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f)) :
    kernelSubmoduleIdeal f E ≤ kerIdeal f := by
  refine generatedIdeal_le ℬ _ fun V e => (mem_kerIdeal f V _).2 ?_
  change (kernelSubmoduleMap f E ≫ underlyingModuleMap f).val.app V e = 0
  rw [Category.assoc, kernel.condition, comp_zero]
  rfl

end KernelIdeals

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

open AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Y : AlgebraicSpaces B S hS}

section KernelMembership

variable {ℬ C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2} (f : ℬ ⟶ C)

/-- The kernel of a morphism of quasi-coherent algebra sheaves is a quasi-coherent module. -/
theorem isQuasicoherentOnSite_algebraKernel (hℬ : ℬ.IsQuasicoherent) (hC : C.IsQuasicoherent) :
    (algebraKernel f).IsQuasicoherentOnSite :=
  have := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS Y.1 Y.2
  ObjectProperty.prop_kernel _ (underlyingModuleMap f) hℬ hC

/-- **Finitely many sections of `ℬ` over an affine étale chart killed by `f : ℬ ⟶ 𝒞` lie in the
sheaf of ideals generated by one finite type quasi-coherent submodule of the kernel**, on a
quasi-compact and quasi-separated algebraic space.  The sections are sections of the kernel, and
the étale extension property behind Stacks 0829
(`AlgebraicGeometry.Space.chartExtensionProperty_id`) puts finitely many of them in one finite type
quasi-coherent submodule. -/
theorem exists_forall_mem_kernelSubmoduleIdeal (hℬ : ℬ.IsQuasicoherent) (hC : C.IsQuasicoherent)
    (hqc : IsQuasiCompactSpace B S hS Y.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
    {W : SmallEtale B S hS Y.1}
    (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj W))
    {κ : Type*} (s : Finset κ) (a : κ → ℬ.right.obj.obj (op W))
    (ha : ∀ i ∈ s, (f.right.hom.app (op W)) (a i) = 0) :
    ∃ E : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f),
      ∀ i ∈ s, a i ∈ (kernelSubmoduleIdeal f E).obj (op W) := by
  classical
  have hKc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _
    (isQuasicoherentOnSite_algebraKernel f hℬ hC)
  have hw : ∀ i, ∃ w : (algebraKernel f).val.obj (op W),
      i ∈ s → (kernel.ι (underlyingModuleMap f)).val.app (op W) w = a i := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨w, hw⟩ := Stacks.SheafOfModules.exists_kernel_section (underlyingModuleMap f)
        (op W) (a i) (ha i hi)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose w hw using hw
  obtain ⟨D, hD⟩ := (chartExtensionProperty_id B.contains_terminal hqc hqs hKc).exists_forall_mem
    hKc s (fun _ => W) (fun _ => W.1.hom)
    (fun _ => Category.comp_id _) (fun _ => hW) w
  let E : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f) :=
    ⟨Subobject.mk (D.toSubmodule (algebraKernel f)).ι,
      D.finiteTypeQuasicoherentSubobjectProperty_mk hKc⟩
  refine ⟨E, fun i hi => ?_⟩
  let k : (D.toSubmodule (algebraKernel f)).toSheafOfModules.val.obj (op W) := ⟨w i, hD i hi⟩
  have heq : (kernelSubmoduleMap f E).val.app (op W)
      ((Subobject.underlyingIso (D.toSubmodule (algebraKernel f)).ι).inv.val.app (op W) k) =
        a i := by
    have h := congrArg (fun φ => φ.val.app (op W) k)
      (Subobject.underlyingIso_arrow (D.toSubmodule (algebraKernel f)).ι)
    change (kernel.ι (underlyingModuleMap f)).val.app (op W)
      (((Subobject.underlyingIso (D.toSubmodule (algebraKernel f)).ι).inv ≫
        (Subobject.mk (D.toSubmodule (algebraKernel f)).ι).arrow).val.app (op W) k) = a i
    rw [h]
    exact hw i hi
  exact heq ▸ app_mem_generatedIdeal ℬ (kernelSubmoduleMap f E) (op W) _

/-- The module of sections of the ideal generated by a submodule of the kernel is
quasi-coherent. -/
private theorem isQuasicoherentOnSite_idealModule_kernelSubmoduleIdeal (hℬ : ℬ.IsQuasicoherent)
    (E : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f)) :
    (idealModule ℬ (kernelSubmoduleIdeal f E)).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_idealModule_generatedIdeal ℬ hℬ E.property.1 _

/-- The quotient by the ideal generated by a submodule of the kernel is of finite presentation. -/
private theorem isFinitePresentation_idealQuotient_kernelSubmoduleIdeal (hℬ : ℬ.IsQuasicoherent)
    (hℬfp : ℬ.IsFinitePresentation)
    (E : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f)) :
    (ℬ.idealQuotient (kernelSubmoduleIdeal f E)).IsFinitePresentation :=
  isFinitePresentation_idealQuotient ℬ _ hℬ
    (isQuasicoherentOnSite_idealModule_kernelSubmoduleIdeal f hℬ E) hℬfp fun W hW =>
      fg_sectionIdeal_generatedIdeal ℬ hℬ E.property.1
        (Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ E.property.2) _ W hW

end KernelMembership

/-! ### One quotient is finite -/

section Integral

variable (A : QuasicoherentAlgebra B S hS Y) {G : Modules.{u, u} B S hS Y.1 Y.2}
  (p : G ⟶ underlyingModule A.obj)

/-- **A finite quasi-coherent algebra on a quasi-compact quasi-separated algebraic space is the
target of a quotient `Sym(𝒢)/(ℰ)` which is finite.**  Over an affine étale chart `U` covering `Y`,
finitely many generators of `𝒢(U)` map to elements of `𝒜(U)` integral over `𝒪_Y(U)`; their monic
equations, evaluated in `Sym(𝒢)(U)`, are sections of the kernel of `Sym(𝒢) ⟶ 𝒜`, and lie in the
sheaf of ideals generated by one finite type quasi-coherent submodule `ℰ` of that kernel.  In
`Sym(𝒢)/(ℰ)` the generators are then integral, so its sections over `U` form a finite module,
and since `U` covers `Y` this makes the quotient of finite type as a module, hence finite over
every affine chart. -/
theorem exists_isIntegral_kernelSubmoduleIdeal_quotient
    (hqc : IsQuasiCompactSpace B S hS Y.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
    (hA : A.obj.IsFinite) (hGqc : G.IsQuasicoherentOnSite)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite G) :
    ∃ E : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2
        (algebraKernel (SymAlgSheaf.algebraLift B S hS Y A.obj G p)),
      ((symmetricAlgebraSheaf B S hS Y G).idealQuotient
        (kernelSubmoduleIdeal (SymAlgSheaf.algebraLift B S hS Y A.obj G p) E)).IsIntegral := by
  classical
  let ℬ := symmetricAlgebraSheaf B S hS Y G
  let f := SymAlgSheaf.algebraLift B S hS Y A.obj G p
  have hℬ : ℬ.IsQuasicoherent := isQuasicoherent_symmetricAlgebraSheaf B S hS Y G hGqc
  have hℬfp : ℬ.IsFinitePresentation :=
    isFinitePresentation_symmetricAlgebraSheaf B S hS Y G hGqc hGfp
  obtain ⟨U, hU, hcov⟩ := SmallEtale.exists_affineObject_coversTop B S hS Y.1 Y.2 hqc
  have hU' : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj U) := hU
  have : Module.FinitePresentation (chartRing B S hS Y.1 Y.2 U) (G.val.obj (op U)) :=
    module_finitePresentation_sections_of_isFinitePresentationOnSite G hGqc hGfp U hU'
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top (R := chartRing B S hS Y.1 Y.2 U)
    (M := G.val.obj (op U)))
  have hint : ∀ e : G.val.obj (op U),
      ∃ P : Polynomial ((structureSheaf B S hS Y.1 Y.2).obj.obj (op U)),
        P.Monic ∧ P.eval₂ (A.obj.algebraMap (op U)) (p.val.app (op U) e) = 0 :=
    fun e => (hA U hU').to_isIntegral (p.val.app (op U) e)
  choose P hPm hP using hint
  let Rr := ((structureSheaf B S hS Y.1 Y.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op U)
  let symU := (commStructureVal B S hS G).obj (op U)
  let eqv := symmetricAlgebraSheafSectionsRingEquiv B S hS Y G hGqc U hU'
  let σ : G.val.obj (op U) → SymmetricAlgebra Rr symU := fun e =>
    (P e).eval₂ (algebraMap Rr (SymmetricAlgebra Rr symU)) (SymmetricAlgebra.ι Rr symU e)
  let b : G.val.obj (op U) → ℬ.right.obj.obj (op U) := fun e => eqv (σ e)
  have hb : ∀ e ∈ t, (f.right.hom.app (op U)) (b e) = 0 := by
    intro e _
    let ψ := (f.right.hom.app (op U)).hom.comp eqv.toRingHom
    have h2 : ψ (σ e) = (P e).eval₂ (ψ.comp (algebraMap Rr (SymmetricAlgebra Rr symU)))
        (ψ (SymmetricAlgebra.ι Rr symU e)) := Polynomial.hom_eval₂ _ _ _ _
    have h3 : ψ.comp (algebraMap Rr (SymmetricAlgebra Rr symU)) = A.obj.algebraMap (op U) :=
      RingHom.ext fun r =>
        algebraLift_symmetricAlgebraSheafSectionsRingEquiv_algebraMap hGqc U hU' A.obj p r
    have h4 : ψ (SymmetricAlgebra.ι Rr symU e) = p.val.app (op U) e :=
      algebraLift_symmetricAlgebraSheafSectionsRingEquiv_ι hGqc U hU' A.obj p e
    exact h2.trans ((congrArg₂ (fun φ x => (P e).eval₂ φ x) h3 h4).trans (hP e))
  obtain ⟨E, hE⟩ := exists_forall_mem_kernelSubmoduleIdeal f hℬ A.property hqc hqs hU' t b hb
  refine ⟨E, ?_⟩
  let I := kernelSubmoduleIdeal f E
  have hIqc := isQuasicoherentOnSite_idealModule_kernelSubmoduleIdeal f hℬ E
  let Cq := ℬ.idealQuotient I
  have hCqc : Cq.IsQuasicoherent := isQuasicoherent_idealQuotient ℬ I hℬ hIqc
  have hCfp : Cq.IsFinitePresentation :=
    isFinitePresentation_idealQuotient_kernelSubmoduleIdeal f hℬ hℬfp E
  have hintU : RingHom.IsIntegral (Cq.algebraMap (op U)) := by
    let : Algebra Rr (Cq.right.obj.obj (op U)) :=
      RingHom.toAlgebra (Cq.algebraMap (op U) : Rr →+* Cq.right.obj.obj (op U))
    let χr : SymmetricAlgebra Rr symU →+* Cq.right.obj.obj (op U) :=
      ((ℬ.toIdealQuotient I).right.hom.app (op U)).hom.comp eqv.toRingHom
    have hχr : ∀ r : Rr, χr (algebraMap Rr (SymmetricAlgebra Rr symU) r) =
        algebraMap Rr (Cq.right.obj.obj (op U)) r := fun r =>
      congrArg ((ℬ.toIdealQuotient I).right.hom.app (op U)).hom
        (symmetricAlgebraSheafSectionsRingEquiv_algebraMap B S hS Y G hGqc U hU' r)
    let χ : SymmetricAlgebra Rr symU →ₐ[Rr] Cq.right.obj.obj (op U) :=
      { χr with commutes' := hχr }
    have hχs : Function.Surjective χ :=
      (surjective_toIdealQuotient_app ℬ I hℬ hIqc U hU').comp eqv.surjective
    have hgen : ∀ e ∈ (t : Set (G.val.obj (op U))),
        _root_.IsIntegral Rr (χ (SymmetricAlgebra.ι Rr symU e)) := by
      intro e he
      refine ⟨P e, hPm e, ?_⟩
      have h1 : χr (σ e) = (P e).eval₂ (χr.comp (algebraMap Rr (SymmetricAlgebra Rr symU)))
          (χr (SymmetricAlgebra.ι Rr symU e)) := Polynomial.hom_eval₂ _ _ _ _
      have h2 : χr (σ e) = 0 :=
        (toIdealQuotient_app_eq_zero_iff ℬ I (op U) (b e)).2 (hE e he)
      have h3 : χr.comp (algebraMap Rr (SymmetricAlgebra Rr symU)) =
          algebraMap Rr (Cq.right.obj.obj (op U)) := RingHom.ext hχr
      exact (congrArg (fun φ => (P e).eval₂ φ (χr (SymmetricAlgebra.ι Rr symU e))) h3).symm.trans
        (h1.symm.trans h2)
    have hIs := Stacks.SymAlg.isIntegral_of_surjective χ hχs (t : Set (G.val.obj (op U))) ht hgen
    exact fun x => hIs.isIntegral x
  have hfinU : RingHom.Finite (Cq.algebraMap (op U)) :=
    RingHom.finite_iff_isIntegral_and_finiteType.2
      ⟨hintU, RingHom.FiniteType.of_finitePresentation (hCfp U hU')⟩
  have hmodU : Module.Finite (chartRing B S hS Y.1 Y.2 U)
      ((underlyingModule Cq).val.obj (op U)) := hfinU
  have hCc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hCqc
  have hCft : SheafOfModules.IsFiniteTypeOnSite (underlyingModule Cq) :=
    isFiniteTypeOnSite_of_coversTop_module_finite_sections (underlyingModule Cq) hCc hcov
      (fun _ => hU') (fun _ => hmodU)
  intro V hV
  have hmodV := module_finite_sections_of_isFiniteTypeOnSite (underlyingModule Cq) hCqc hCft V hV
  have hfinV : RingHom.Finite (Cq.algebraMap (op V)) := hmodV
  exact hfinV.to_isIntegral

end Integral

/-! ### The data of the proof of Stacks 086Z -/

section Data

variable (A : QuasicoherentAlgebra B S hS Y) {G : Modules.{u, u} B S hS Y.1 Y.2}
  (p : G ⟶ underlyingModule A.obj)

/-- **The data of the proof of Stacks 086Z, from a quasi-coherent module of finite presentation
surjecting onto the algebra.**  With `ℬ = Sym(𝒢)` and `ℬ ⟶ 𝒜` induced by `𝒢 ↠ 𝒜`, the sheaves of
ideals generated by the finite type quasi-coherent submodules of the kernel form a filtered
family, indexed by a small model of those submodules, whose quotients are quasi-coherent of finite
presentation, whose cocone over `𝒜` is colimiting, and one of whose quotients is integral. -/
theorem exists_idealQuotient_system_of_epi (hqc : IsQuasiCompactSpace B S hS Y.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
    (hA : A.obj.IsFinite) (hGqc : G.IsQuasicoherentOnSite)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite G) (hp : Epi p) :
    ∃ (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (f : ℬ ⟶ A.obj) (J : Type u)
      (inst : SmallCategory J),
      let _ := inst
      ∃ (_ : IsFiltered J) (ι : J → ℬ.IdealSheaf)
        (hι : ∀ j j' : J, (j ⟶ j') → ι j ≤ ι j')
        (hkill : ∀ (j : J) (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
          a ∈ (ι j).obj U → (f.right.hom.app U).hom a = 0)
        (hqcoh : ∀ j, (ℬ.idealQuotient (ι j)).IsQuasicoherent),
        (∀ j, (ℬ.idealQuotient (ι j)).IsFinitePresentation) ∧
        (∃ j, (ℬ.idealQuotient (ι j)).IsIntegral) ∧
        Nonempty (IsColimit (Cocone.mk A
          (idealQuotientQcohCocone ℬ ι hι A f hkill hqcoh))) := by
  classical
  let ℬ := symmetricAlgebraSheaf B S hS Y G
  let f := SymAlgSheaf.algebraLift B S hS Y A.obj G p
  have hℬ : ℬ.IsQuasicoherent := isQuasicoherent_symmetricAlgebraSheaf B S hS Y G hGqc
  have hℬfp : ℬ.IsFinitePresentation :=
    isFinitePresentation_symmetricAlgebraSheaf B S hS Y G hGqc hGfp
  have hK : (algebraKernel f).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_algebraKernel f hℬ A.property
  have : IsFiltered (FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f)) :=
    isFiltered_finiteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f)
  have : EssentiallySmall.{u}
      (FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f)) :=
    essentiallySmall_finiteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f)
  let e := equivSmallModel.{u}
    (FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f))
  have : IsFiltered (SmallModel.{u}
      (FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f))) :=
    IsFiltered.of_equivalence e
  let ι : SmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (algebraKernel f)) →
      ℬ.IdealSheaf := fun j => kernelSubmoduleIdeal f (e.inverse.obj j)
  have hι : ∀ j j', (j ⟶ j') → ι j ≤ ι j' := fun j j' h =>
    kernelSubmoduleIdeal_mono f (e.inverse.map h)
  have hιE : ∀ E, ι (e.functor.obj E) = kernelSubmoduleIdeal f E := fun E =>
    le_antisymm (kernelSubmoduleIdeal_mono f (e.unitInv.app E))
      (kernelSubmoduleIdeal_mono f (e.unit.app E))
  have hkill : ∀ (j) (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
      a ∈ (ι j).obj U → (f.right.hom.app U).hom a = 0 := fun j U a ha =>
    apply_eq_zero_of_le_kerIdeal f (kernelSubmoduleIdeal_le_kerIdeal f _) U a ha
  have hqcoh : ∀ j, (ℬ.idealQuotient (ι j)).IsQuasicoherent := fun j =>
    isQuasicoherent_idealQuotient ℬ (ι j) hℬ
      (isQuasicoherentOnSite_idealModule_kernelSubmoduleIdeal f hℬ _)
  refine ⟨ℬ, f, _, inferInstance, inferInstance, ι, hι, hkill, hqcoh, fun j =>
    isFinitePresentation_idealQuotient_kernelSubmoduleIdeal f hℬ hℬfp _, ?_, ?_⟩
  · obtain ⟨E, hE⟩ := exists_isIntegral_kernelSubmoduleIdeal_quotient A p hqc hqs hA hGqc hGfp
    exact ⟨e.functor.obj E, by rwa [hιE]⟩
  · refine nonempty_isColimit_idealQuotientQcohCocone_of_locally ℬ ι hι A f hkill hqcoh
      (isLocallySurjective_algebraLift hGqc A.obj p A.property hp) fun U a ha => ?_
    refine (SmallEtale.topology B S hS Y.1).superset_covering ?_
      (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS Y.1 U.unop)
    intro W' g hg
    obtain ⟨O, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    refine (Stacks.Sites.memSieve (O := ℬ.right) ι a).downward_closed ?_ k
    let incl := openChartInclusion B S hS Y.1 U.unop O.down.1
    have hW := isAffine_chartScheme_openChart B S hS Y.1 U.unop O.down
    have hfa : (f.right.hom.app (op (openChart B S hS Y.1 U.unop O.down.1)))
        (ℬ.right.obj.map incl.op a) = 0 := by
      refine (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _) a)
        (f.right.hom.naturality incl.op)).trans ?_
      change A.obj.right.obj.map incl.op ((f.right.hom.app U) a) = 0
      rw [ha, map_zero]
    obtain ⟨E, hE⟩ := exists_forall_mem_kernelSubmoduleIdeal f hℬ A.property hqc hqs hW
      ({()} : Finset Unit) (fun _ => ℬ.right.obj.map incl.op a) (fun _ _ => hfa)
    exact ⟨e.functor.obj E, by rw [hιE]; exact hE () (Finset.mem_singleton_self _)⟩

end Data

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 086Z from a quasi-coherent module of finite presentation surjecting onto the
algebra.**  The data of `AlgebraicGeometry.Space.exists_idealQuotient_system_of_epi` are turned
into the directed system by
`AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective`. -/
theorem exists_directed_isFinite_isFinitePresentation_locallySurjective_of_epi
    (Y : AlgebraicSpaces B S hS) (A : QuasicoherentAlgebra B S hS Y)
    (hqc : IsQuasiCompactSpace B S hS Y.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj)
    (hA : A.obj.IsFinite) (G : Modules.{u, u} B S hS Y.1 Y.2) (hGqc : G.IsQuasicoherentOnSite)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (p : G ⟶ AlgebraSheaf.underlyingModule A.obj) (hp : Epi p) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ QuasicoherentAlgebra B S hS Y) (φ : D ⟶ (Functor.const I).obj A),
      Nonempty (IsColimit (Cocone.mk A φ)) ∧
      (∀ i, (D.obj i).obj.IsFinite ∧ (D.obj i).obj.IsFinitePresentation) ∧
      ∀ i j (h : i ≤ j), Presheaf.IsLocallySurjective
        (SmallEtale.topology B S hS Y.obj) (D.map (homOfLE h)).hom.right.hom :=
  exists_directed_isFinite_isFinitePresentation_locallySurjective B S hS Y A hqc hqs hA
    (fun _ _ _ => exists_idealQuotient_system_of_epi A p hqc hqs hA hGqc hGfp hp)

/-- The underlying module of a finite quasi-coherent algebra is of finite type. -/
theorem isFiniteTypeOnSite_underlyingModule_of_isFinite {Y : AlgebraicSpaces B S hS}
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (hAq : A.IsQuasicoherent) (hA : A.IsFinite) :
    SheafOfModules.IsFiniteTypeOnSite (AlgebraSheaf.underlyingModule A) :=
  isFiniteTypeOnSite_of_module_finite_sections _
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hAq)
    fun W hW => (hA W hW : _)

end AlgebraicGeometry.Space
