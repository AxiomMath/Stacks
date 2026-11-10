module

public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.Twists
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sheaf associated with a finite graded module on a homogeneous spectrum is of finite type

`StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.Twists` proves that the twisting sheaves
`𝒪(t)` on `Proj 𝒜` are of finite type when `𝒜` is a finite type algebra over `𝒜₀`. This file proves
the same for the sheaf `M̃` associated with any finite graded `A`-module `M`, by the same argument:
on a standard open `D₊(f)` the sections of `M̃` are the degree-zero localization `M₍f₎`, which is a
finite module over `A₍f₎` by [Stacks, Tag 07Z2] (2) (`moduleLocalization_away_finite`).

The twisting sheaf is the case `M = A(t)`; the statements there are left as they stand.

* `GradedModule.moduleToSubmodules`: a `SetLike` grading of a module, promoted to a grading by
  submodules over any base ring mapping into degree zero. `GradedModule.toSubmodules` is the case
  of the regular module.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.finite_degreeZeroLocalization`
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.finite_associatedModuleSheafSections`
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.isFiniteType_associatedModuleSheaf`

## References

* [Stacks Project, Tag 07Z2](https://stacks.math.columbia.edu/tag/07Z2)
* [Stacks Project, Tag 07ZY](https://stacks.math.columbia.edu/tag/07ZY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Stacks.GradedLocalization

universe u w

namespace GradedModule

variable {R A M σ τ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ M] [AddSubgroupClass τ M]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (𝒨 : ℤ → τ) [SetLike.GradedSMul 𝒜 𝒨]
  (h0 : ∀ r : R, algebraMap R A r ∈ 𝒜 0)

/-- **A grading of a module whose compatibility with a `SetLike` ring grading is known is a
grading by submodules over any base ring mapping into degree zero.** The `i`-th member is the
`i`-th graded piece, with the same underlying set; it is stable under the `R`-action because
`r • x = (algebraMap R A r) • x` and a degree-zero scalar preserves degrees.

This is the module analogue of `GradedRing.toSubmodules`, and it is the form of a graded module
that `moduleLocalization_away_finite` consumes. The regular module regraded by a shift — the case
the degree-zero localization of a twisting sheaf needs — is the instance `M = A`. -/
@[ega "II 2.4.5" "if A → S lands in S_0"]
public def moduleToSubmodules (i : ℤ) : Submodule R M where
  carrier := 𝒨 i
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' r x hx := by
    rw [← IsScalarTower.algebraMap_smul A r x]
    simpa using SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝒨) (h0 r) hx

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The promoted grading has the same members as the original one. -/
@[simp] public theorem mem_moduleToSubmodules {i : ℤ} {x : M} :
    x ∈ moduleToSubmodules 𝒜 𝒨 h0 i ↔ x ∈ 𝒨 i := Iff.rfl

/-- The promoted grading decomposes the module: the members, and hence the homogeneous
decomposition, are unchanged. -/
public instance instDecompositionModuleToSubmodules [DirectSum.Decomposition 𝒨] :
    DirectSum.Decomposition (moduleToSubmodules 𝒜 𝒨 h0) where
  decompose' := DirectSum.decompose 𝒨
  left_inv := DirectSum.Decomposition.left_inv
  right_inv := DirectSum.Decomposition.right_inv

/-- The promoted gradings are compatible, the members being unchanged on both sides. -/
public instance instGradedSMulModuleToSubmodules :
    SetLike.GradedSMul (GradedRing.toSubmodules 𝒜 h0) (moduleToSubmodules 𝒜 𝒨 h0) :=
  ⟨SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝒨)⟩

end GradedModule

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

section Module

variable {M : Type u} {τ : Type*} [AddCommGroup M] [Module A M]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- **The degree-zero localization of a finite graded module at a homogeneous element of positive
degree is a finite module over the degree-zero localization of the ring**, when the ring is a
finite type algebra over its degree-zero part.

This is the local, ring-theoretic content of the second assertion of Stacks tag 07ZY, and it is
Stacks tag 07Z2 (2) — `moduleLocalization_away_finite` — read through the two identifications
that separate the two spellings of the degree-zero localization: the gradings are promoted to
submodule-valued ones by `GradedRing.toSubmodules` and `GradedModule.moduleToSubmodules`, which
changes no member, and the degree-zero localizations of the ring are matched by
`HomogeneousLocalization.Away.toSubmodulesEquiv`, which changes no fraction. -/
public theorem finite_degreeZeroLocalization [Algebra.FiniteType (𝒜 0) A] [Module.Finite A M]
    {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    Module.Finite (HomogeneousLocalization.Away 𝒜 f)
      (GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) := by
  classical
  let h0 : ∀ r : 𝒜 0, algebraMap (𝒜 0) A r ∈ 𝒜 0 := fun r => r.2
  let : Module (𝒜 0) M := Module.compHom (R := A) M (algebraMap (𝒜 0) A)
  have : IsScalarTower (𝒜 0) A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- the action on the ambient localized module, as `GradedModuleDegreeZeroLocalization` takes it
  let : Module (HomogeneousLocalization.Away 𝒜 f) (LocalizedModule.Away (R := A) f M) :=
    Module.compHom (R := Localization.Away f) (LocalizedModule.Away (R := A) f M)
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  let 𝒜' := GradedRing.toSubmodules 𝒜 h0
  let ℳ' := GradedModule.moduleToSubmodules (R := 𝒜 0) 𝒜 𝒨 h0
  have hf' : f ∈ 𝒜' d := hf
  have key : Module.Finite (SLoc 𝒜' f) (MLoc 𝒜' ℳ' f d) :=
    moduleLocalization_away_finite 𝒜' ℳ' f d hf' hd
  have hmem : ∀ y, y ∈ MLoc 𝒜' ℳ' f d ↔
      y ∈ GradedModuleDegreeZeroLocalization 𝒜 𝒨 f := by
    intro y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨n, x, hx, rfl⟩ := (mem_MLoc_iff 𝒜' ℳ' f d hf' y).mp hy
      exact Submodule.subset_span
        ⟨d, n, hf, x, hx, rfl⟩
    · obtain ⟨n, x, hx, he⟩ := degreeZeroFraction_surjective 𝒜 𝒨 hf ⟨y, hy⟩
      have hy' : deg0frac f n x = y := congrArg Subtype.val he
      exact hy' ▸ deg0frac_mem_MLoc 𝒜' ℳ' f d n x hx
  let ε := (HomogeneousLocalization.Away.toSubmodulesEquiv 𝒜 h0 f).symm
  have hval : ∀ r : SLoc 𝒜' f, (ε r).val = r.val := fun r => by
    simpa [ε] using (HomogeneousLocalization.Away.val_toSubmodulesEquiv 𝒜 h0 f (ε r)).symm
  have hsmul : ∀ (r : SLoc 𝒜' f) (z : MLocAll f (M := M)), r • z = (ε r) • z := by
    intro r z
    change r.val • z = (ε r).val • z
    rw [hval]
  exact Module.Finite.of_addEquiv ε.toRingHom
    { toFun := fun x => ⟨x.1, (hmem x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).mpr x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl } (fun r x => Subtype.ext (hsmul r x.1)) key

/-- **The sections of the associated sheaf of a finite graded module over a standard open at a
homogeneous element of positive degree are a finite module over the degree-zero localization
there**, when the graded ring is a finite type algebra over its degree-zero part.

The sections over `D₊(f)` are the degree-zero localization `M₍f₎`, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`, and that
identification is linear over `HomogeneousLocalization.Away 𝒜 f`. -/
public theorem finite_associatedModuleSheafSections [Algebra.FiniteType (𝒜 0) A]
    [Module.Finite A M] {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    Module.Finite (HomogeneousLocalization.Away 𝒜 f)
      ((associatedModuleSheaf 𝒜 𝒨).val.obj (.op (ProjectiveSpectrum.basicOpen 𝒜 f))) := by
  have := finite_degreeZeroLocalization 𝒜 𝒨 hd hf
  exact Module.Finite.equiv (associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd).symm

end Module

section ModuleFiniteType

variable {M : Type u} {τ : Type*} [AddCommGroup M] [Module A M]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- **The sheaf associated with a finite graded module on a homogeneous spectrum is a finite-type
module sheaf** when the graded ring is a finite type algebra over its degree-zero part.

Finite type is local, and the standard opens `D₊(f)` at the homogeneous elements `f` of positive
degree are affine opens covering `Proj 𝒜`. Over one of them the sections of `M̃` are a finite
module over the degree-zero localization `M₍f₎`
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.finite_associatedModuleSheafSections`), hence over the
functions on `D₊(f)`, which `AlgebraicGeometry.Proj.basicOpenIsoAway` identifies with `A₍f₎` by
the very map that defines the action. -/
public theorem isFiniteType_associatedModuleSheaf [Algebra.FiniteType (𝒜 0) A]
    [Module.Finite A M] :
    SheafOfModules.IsFiniteType.{u, u, u} (associatedModuleSheaf 𝒜 𝒨) := by
  let F : (AlgebraicGeometry.Proj 𝒜).Modules := associatedModuleSheaf 𝒜 𝒨
  have : F.IsQuasicoherent :=
    (inferInstance : SheafOfModules.IsQuasicoherent.{u, u, u} (associatedModuleSheaf 𝒜 𝒨))
  refine Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn F
    (fun i : Σ m : ℕ+, 𝒜 (m : ℕ) => Proj.basicOpen 𝒜 (i.2 : A))
    (IsOpenCover.mk (Proj.iSup_basicOpen_homogeneous_eq_top 𝒜))
    (fun i => Proj.isAffineOpen_basicOpen 𝒜 _ i.2.2 i.1.2) fun i => ?_
  let _ : Module (HomogeneousLocalization.Away 𝒜 (i.2 : A))
      Γ(F, Proj.basicOpen 𝒜 (i.2 : A)) :=
    associatedModuleSheafStandardOpenModule 𝒜 𝒨 (i.2 : A)
  let ε : HomogeneousLocalization.Away 𝒜 (i.2 : A) ≃+*
      Γ(AlgebraicGeometry.Proj 𝒜, Proj.basicOpen 𝒜 (i.2 : A)) :=
    (Proj.basicOpenIsoAway 𝒜 (i.2 : A) i.2.2 i.1.2).commRingCatIsoToRingEquiv
  have hfin : Module.Finite Γ(AlgebraicGeometry.Proj 𝒜, Proj.basicOpen 𝒜 (i.2 : A))
      Γ(F, Proj.basicOpen 𝒜 (i.2 : A)) :=
    Module.Finite.of_addEquiv ε.toRingHom (AddEquiv.refl _) (fun _ _ => rfl)
      (finite_associatedModuleSheafSections 𝒜 𝒨 i.1.2 i.2.2)
  have haff := Proj.isAffineOpen_basicOpen 𝒜 _ i.2.2 i.1.2
  exact Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_finite_specModule F _ haff
    (Module.Finite.equiv (Stacks.AlgebraicGeometry.CoherentFinite.specSectionsEquiv F haff).symm)

end ModuleFiniteType

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
