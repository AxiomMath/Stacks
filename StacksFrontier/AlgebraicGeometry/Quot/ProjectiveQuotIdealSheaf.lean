module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasicoherentIdealSheafData.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Functor

/-!
# A member of `Quot_{𝒪/ℙⁿ/ℤ}(T)` is a sheaf of ideals, and cuts out a closed subscheme

`AlgebraicGeometry.ProjectiveQuot.families n 1 T` records `Quot_{𝒪/ℙⁿ/ℤ}(T)` on kernels: a
submodule `K ⊆ 𝒪^{⊕ 1}` of the rank-one free module on `ℙⁿ_T` whose quotient is of finite
presentation and flat over `T`, as a `CategoryTheory.Subobject`. The universal family of the
Hilbert space of `ℙⁿ_ℤ/ℤ` is the closed subscheme of `ℙⁿ_T` such a member cuts out, and the
passage from the one to the other begins here: the subobject is read as a quasi-coherent sheaf of
ideals of `𝒪_{ℙⁿ_T}` and fed to Stacks 01QQ.

The two steps are:

* **reading the subobject as a sheaf of ideals.** The rank-one free module is the structure sheaf
  (`AlgebraicGeometry.ProjectiveQuot.freeModuleOneIso`), and subobjects of a module on a scheme
  are its subsheaves (`AlgebraicGeometry.Scheme.Modules.subobjectSubmodule`). The resulting sheaf
  of ideals is `AlgebraicGeometry.ProjectiveQuot.idealOfFamily`.
* **quasi-coherence.** A subobject is the kernel of the projection onto its own quotient
  (`CategoryTheory.Limits.kernelSubobject_cokernel_π`), and the quotient of a member of `families`
  is of finite presentation, hence quasi-coherent (Stacks 01BW); so that kernel is quasi-coherent
  (Stacks 01LB, kernel half) and with it the sheaf of ideals
  (`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_subobjectSubmodule`).

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.freeModuleOneIso`: `𝒪^{⊕ 1} ≅ 𝒪` on `ℙⁿ_T`.
* `AlgebraicGeometry.ProjectiveQuot.unitSubobject`: a subobject of `𝒪^{⊕ 1}`, read in `𝒪`.
* `AlgebraicGeometry.ProjectiveQuot.idealOfFamily`: the sheaf of ideals of `𝒪_{ℙⁿ_T}` it cuts out.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.isQuasicoherent_underlying`: the underlying module of a
  subobject of `𝒪^{⊕ 1}` whose quotient is of finite presentation is quasi-coherent.
* `AlgebraicGeometry.ProjectiveQuot.isQuasicoherent_idealOfFamily`: so is the sheaf of ideals.
* `AlgebraicGeometry.ProjectiveQuot.exists_isClosedImmersion_ker_eq_idealOfFamily`: **a member of
  `Quot_{𝒪/ℙⁿ/ℤ}(T)` cuts out a closed subscheme of `ℙⁿ_T`**, whose sheaf of ideals on every
  affine open is the ideal of sections of the member.

## Implementation notes

Only finite presentation of the quotient is used, not its flatness over `T`, so the statements
below take that hypothesis rather than membership in
`AlgebraicGeometry.ProjectiveQuot.families`; the membership form is the corollary
`AlgebraicGeometry.ProjectiveQuot.exists_isClosedImmersion_ker_eq_idealOfFamily_of_mem`.

The sheaf of ideals is attached to the subobject `AlgebraicGeometry.ProjectiveQuot.unitSubobject`
of the *structure sheaf* rather than to the given subobject of `𝒪^{⊕ 1}`, because
`AlgebraicGeometry.Scheme.Modules.subobjectSubmodule` produces a subsheaf of the ambient module
of its argument and `Stacks.Divisors.idealSheafDataOfSubmodule` consumes a subsheaf of the
structure sheaf. The comparison of the two ambient modules is
`AlgebraicGeometry.ProjectiveQuot.freeModuleOneIso`, which is
`CategoryTheory.Limits.coproductUniqueIso` at `Fin 1`.

## References

* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 01LB](https://stacks.math.columbia.edu/tag/01LB)
* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n : ℕ} {T : Scheme.{u}}

/-- Quasi-coherence transfers along an isomorphism of modules on `ℙⁿ_T`. -/
private theorem isQuasicoherent_of_iso {M N : (projectiveSpaceOver n T).Modules} (e : M ≅ N)
    [N.IsQuasicoherent] : M.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (projectiveSpaceOver n T).ringCatSheaf).prop_of_iso e.symm
    inferInstance

/-- **The rank-one free module on `ℙⁿ_T` is its structure sheaf.** The coproduct over `Fin 1` is
its single summand. -/
def freeModuleOneIso (n : ℕ) (T : Scheme.{u}) :
    freeModule n 1 T ≅ Scheme.unitModule (projectiveSpaceOver n T) :=
  coproductUniqueIso fun _ : Fin 1 => Scheme.unitModule (projectiveSpaceOver n T)

/-- **A subobject of `𝒪^{⊕ 1}` on `ℙⁿ_T`, read as a subobject of the structure sheaf** along
`AlgebraicGeometry.ProjectiveQuot.freeModuleOneIso`. -/
abbrev unitSubobject (K : Subobject (freeModule n 1 T)) :
    Subobject (Scheme.unitModule (projectiveSpaceOver n T)) :=
  Subobject.mk (K.arrow ≫ (freeModuleOneIso n T).hom)

/-- **The sheaf of ideals of `𝒪_{ℙⁿ_T}` cut out by a subobject of `𝒪^{⊕ 1}`.** -/
def idealOfFamily (K : Subobject (freeModule n 1 T)) :
    (Scheme.unitModule (projectiveSpaceOver n T)).Submodule :=
  Scheme.Modules.subobjectSubmodule (unitSubobject K)

/-- The underlying module of a subobject of `𝒪^{⊕ 1}` is the kernel of the projection onto its
quotient. -/
def underlyingIsoKernelQuotientπ (K : Subobject (freeModule n 1 T)) :
    (K : (projectiveSpaceOver n T).Modules) ≅ kernel (quotientπ K) :=
  eqToIso (congrArg (fun L : Subobject (freeModule n 1 T) =>
    (L : (projectiveSpaceOver n T).Modules)) (kernelSubobject_cokernel_π K).symm) ≪≫
    kernelSubobjectIso (quotientπ K)

/-- **The underlying module of a subobject of `𝒪^{⊕ 1}` with quotient of finite presentation is
quasi-coherent**: it is the kernel of the projection onto that quotient, which is quasi-coherent
by Stacks 01BW, so Stacks 01LB applies. -/
theorem isQuasicoherent_underlying (K : Subobject (freeModule n 1 T))
    (hK : (quotient K).IsFinitePresentation) :
    (K : (projectiveSpaceOver n T).Modules).IsQuasicoherent := by
  have := hK
  have : (quotient K).IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation _
  have : (freeModule n 1 T).IsQuasicoherent := isQuasicoherent_of_iso (freeModuleOneIso n T)
  exact isQuasicoherent_of_iso (underlyingIsoKernelQuotientπ K)

/-- The underlying module of `AlgebraicGeometry.ProjectiveQuot.unitSubobject` is the underlying
module of the subobject it comes from. -/
def underlyingUnitSubobjectIso (K : Subobject (freeModule n 1 T)) :
    (unitSubobject K : (projectiveSpaceOver n T).Modules) ≅
      (K : (projectiveSpaceOver n T).Modules) :=
  Subobject.underlyingIso (K.arrow ≫ (freeModuleOneIso n T).hom)

/-- **The sheaf of ideals of a subobject of `𝒪^{⊕ 1}` with quotient of finite presentation is
quasi-coherent.** -/
theorem isQuasicoherent_idealOfFamily (K : Subobject (freeModule n 1 T))
    (hK : (quotient K).IsFinitePresentation) :
    (idealOfFamily K).toSheafOfModules.IsQuasicoherent := by
  have := isQuasicoherent_underlying K hK
  have : (unitSubobject K : (projectiveSpaceOver n T).Modules).IsQuasicoherent :=
    isQuasicoherent_of_iso (underlyingUnitSubobjectIso K)
  exact Scheme.Modules.isQuasicoherent_subobjectSubmodule (unitSubobject K)

/-- **A subobject of `𝒪^{⊕ 1}` on `ℙⁿ_T` with quotient of finite presentation cuts out a closed
subscheme of `ℙⁿ_T`**, whose sheaf of ideals on every affine open is the ideal of sections of the
subobject. This is Stacks 01QQ applied to
`AlgebraicGeometry.ProjectiveQuot.idealOfFamily`. -/
theorem exists_isClosedImmersion_ker_eq_idealOfFamily (K : Subobject (freeModule n 1 T))
    (hK : (quotient K).IsFinitePresentation) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ projectiveSpaceOver n T), IsClosedImmersion i ∧
      ∀ U : (projectiveSpaceOver n T).affineOpens,
        RingHom.ker (i.app U.1).hom = (idealOfFamily K).obj (op U.1) :=
  @Stacks.Divisors.exists_isClosedImmersion_ker_eq _ (idealOfFamily K)
    (isQuasicoherent_idealOfFamily K hK)

/-- **A member of `Quot_{𝒪/ℙⁿ/ℤ}(T)` cuts out a closed subscheme of `ℙⁿ_T`.** -/
theorem exists_isClosedImmersion_ker_eq_idealOfFamily_of_mem {K : Subobject (freeModule n 1 T)}
    (hK : K ∈ families n 1 T) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ projectiveSpaceOver n T), IsClosedImmersion i ∧
      ∀ U : (projectiveSpaceOver n T).affineOpens,
        RingHom.ker (i.app U.1).hom = (idealOfFamily K).obj (op U.1) :=
  exists_isClosedImmersion_ker_eq_idealOfFamily K hK.1

end AlgebraicGeometry.ProjectiveQuot

end
