module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectSupportedExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentHomotopyColimit
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonExactFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# A perfect object on a quasi-compact open is a direct summand of a restriction

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and `W ⊆ X` a
quasi-compact open subspace. Every perfect object `P` of `D(𝒪_W)` is a direct summand of the
restriction `R|_W` of a perfect object `R` of `D(𝒪_X)` (Stacks 09IX).

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_restrict_iso_biprod_of_isPerfect`: **Stacks 09IX**.

## Implementation notes

The proof is the source's: this is the special case of Stacks 09IV
(`AlgebraicGeometry.Space.exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts`)
with `T = |X|` and `E = 0`, the map `P ⟶ E|_W` being zero. The closed subset `T = |X|` is
admissible because the empty open subspace has quasi-compact inclusion
(`AlgebraicGeometry.Space.isQuasiCompact_ι_openSubspacesOrderIso_symm_compl_univ`), every object
is supported on `|W|`, and `0` lies in `D_QCoh(𝒪_X)`.

"`P` is a direct summand of `R|_W`" is read as an isomorphism `R|_W ≅ P ⊞ C` in `D(𝒪_W)` for some
object `C`. Restriction to the open subspace `W` is étale restriction of modules along its
inclusion, `AlgebraicGeometry.Space.openSubspaceHom`, applied on derived categories.

**The models of `D(𝒪_X)` and `D(𝒪_W)`** are arbitrary. Stacks 09IV is stated at the standard
models; its output is carried to the given models along the comparison equivalences
`StacksDraft.DerivedModel.modelEquiv`, which identify the localization functors
(`StacksDraft.DerivedModel.modelCompQIso`, `StacksDraft.DerivedModel.modelInverseCompQIso`, so
that perfectness is preserved) and commute with restriction
(`StacksDraft.DerivedModel.modelEquivCompMapDerivedCategoryIso`,
`StacksDraft.DerivedModel.mapDerivedCategoryCompModelEquivIso`).

## References

* [Stacks Project, Tag 09IX](https://stacks.math.columbia.edu/tag/09IX)
* [Stacks Project, Tag 09IV](https://stacks.math.columbia.edu/tag/09IV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StacksDraft.DerivedModel

universe w w' u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] pointTopology smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

/-- **Stacks 09IX.** Let `S` be a scheme, `X` a quasi-compact and quasi-separated algebraic space
over `S` and `W ⊆ X` a quasi-compact open subspace. Let `P` be a perfect object of `D(𝒪_W)`.
Then `P` is a direct summand of the restriction of a perfect object of `D(𝒪_X)`: there are a
perfect `R` in `D(𝒪_X)` and an object `C` of `D(𝒪_W)` with `R|_W ≅ P ⊕ C`. Both derived
categories are taken at arbitrary models; quasi-separation is absolute, over the final object of
the base category of schemes. -/
@[stacks 09IX]
theorem exists_isPerfect_restrict_iso_biprod_of_isPerfect
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W)
    (hWqc : IsQuasiCompactSpace B S hS W.toFunctor)
    [hDX : HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)]
    [hDW : HasDerivedCategory.{w'} (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2)]
    (P : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2))
    (hP : (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2).IsPerfect P) :
    ∃ R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect R ∧
      ∃ C : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2),
        Nonempty ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R ≅ P ⊞ C) := by
  -- the biproducts of the given model, fixed before the standard models enter the context
  have hbi : ∀ A C : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2), HasBinaryBiproduct A C := fun _ _ => inferInstance
  let F := etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
    (isEtale_openSubspaceHom B S hS W hW)
  let stdX := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let stdW := HasDerivedCategory.standard (Modules.{u, u} B S hS
    (openSubspaceSpace B S hS W hW).1 (openSubspaceSpace B S hS W hW).2)
  let ΨX := modelEquiv stdX hDX
  let ΨW := modelEquiv stdW hDW
  -- the perfect object `P` at the standard model
  obtain ⟨Pc, hPc, ⟨eP⟩⟩ := hP
  let P₀ := ΨW.inverse.obj P
  -- the zero object of `D_QCoh(𝒪_X)`, at the standard model
  obtain ⟨Z, hZ₀⟩ :=
    (inferInstance : HasZeroObject (@DerivedCategory (Modules.{u, u} B S hS X.1 X.2) _ _ stdX)).zero
  let E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
    ⟨Z, fun i => SheafOfModules.IsQuasicoherentOnSite.of_isZero
      ((@DerivedCategory.homologyFunctor _ _ _ stdX i).map_isZero hZ₀)⟩
  obtain ⟨R₀, -, hR₀, -, C₀, e, -, -⟩ :=
    exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts B.contains_terminal X hXqc
      hXqs W hW hWqc Set.univ isClosed_univ
      (isQuasiCompact_ι_openSubspacesOrderIso_symm_compl_univ B S hS X.1 X.2) E P₀
      ⟨Pc, hPc, ⟨((modelInverseCompQIso stdW hDW).app Pc).symm ≪≫ ΨW.inverse.mapIso eP⟩⟩
      (fun _ => Set.subset_univ _) 0
  -- carry `R₀` to the given model of `D(𝒪_X)`
  obtain ⟨Rc, hRc, ⟨eR⟩⟩ := hR₀
  refine ⟨ΨX.functor.obj R₀, ⟨Rc, hRc, ⟨((modelCompQIso stdX hDX).app Rc).symm ≪≫
    ΨX.functor.mapIso eR⟩⟩, ΨW.functor.obj C₀, ⟨?_⟩⟩
  have := preservesBinaryBiproduct_of_preservesBinaryProduct ΨW.functor (X := P₀) (Y := C₀)
  exact (modelEquivCompMapDerivedCategoryIso F stdX hDX hDW).app R₀ ≪≫
    ((mapDerivedCategoryCompModelEquivIso F stdX stdW hDW).app R₀).symm ≪≫
    ΨW.functor.mapIso e ≪≫ ΨW.functor.mapBiprod P₀ C₀ ≪≫
    biprod.mapIso (ΨW.counitIso.app P) (Iso.refl _)

end AlgebraicGeometry.Space

end
