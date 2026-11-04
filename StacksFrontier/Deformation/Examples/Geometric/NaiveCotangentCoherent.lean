module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.DeRham.CoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyQuasicoherent

/-!
# The cohomology sheaves of the naive cotangent complex are coherent

Let `f : X ⟶ Y` be a morphism of schemes locally of finite type over a locally Noetherian `Y`.
Then every cohomology sheaf `H^i(NL_{X/Y})` of the naive cotangent complex is a coherent
`𝒪_X`-module. This is the input the proof of [Stacks Project, Tag 0DYA] takes from
[Stacks Project, Tag 0D0K]: "`NL_{X/k}` has coherent cohomology sheaves zero except in degrees
`0` and `-1`".

The proof is the source's. Degrees other than `-1` and `0` are zero
(`AlgebraicGeometry.Scheme.isZero_homology_naiveCotangentComplex`). Degree `0` is `Ω_{X/Y}`
([Stacks Project, Tag 0D0J]), which is coherent. In degree `-1` the sheaf is quasi-coherent
(the quasi-coherence clause of Tag 0D0J), so on the locally Noetherian scheme `X` it suffices to
show it is of finite type, which is local. Locally on `X`, [Stacks Project, Tag 0D0K] makes
`NL_{X/Y}` quasi-isomorphic to a two-term complex `ℱ₋₁ ⟶ ℱ₀` of quasi-coherent modules with
`ℱ₋₁` of finite type, so there `H^{-1}(NL_{X/Y})` is the kernel of a map from a module of finite
type to a quasi-coherent module, which is of finite type on a locally Noetherian scheme.

## Main results

* `AlgebraicGeometry.Scheme.isFiniteType_homology_naiveCotangentComplex_negOne`: `H^{-1}` is of
  finite type, for `f` locally of finite presentation and `X` locally Noetherian.
* `AlgebraicGeometry.Scheme.isCoherent_homology_naiveCotangentComplex`: every cohomology sheaf
  of `NL_{X/Y}` is coherent, for `f` locally of finite type over a locally Noetherian `Y`.

## References

* [Stacks Project, Tag 0D0K](https://stacks.math.columbia.edu/tag/0D0K)
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J)
* [Stacks Project, Tag 0DYA](https://stacks.math.columbia.edu/tag/0DYA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.NaiveCotangentAffineIso

universe u

namespace AlgebraicGeometry.Scheme

/-- **`H^{-1}(NL_{X/Y})` is of finite type** when `f` is locally of finite presentation and `X`
is locally Noetherian. Finite type is local; on an affine open `V` as in
[Stacks Project, Tag 0D0K] the restriction of `H^{-1}(NL_{X/Y})` is the degree `-1` cohomology
sheaf of a two-term complex `ℱ₋₁ ⟶ ℱ₀` of quasi-coherent modules with `ℱ₋₁` of finite type, that
is the kernel of `ℱ₋₁ ⟶ ℱ₀`, which is of finite type because `V` is locally Noetherian. -/
theorem isFiniteType_homology_naiveCotangentComplex_negOne {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [IsLocallyNoetherian X] :
    ((naiveCotangentComplex f).homology (-1)).IsFiniteType := by
  have key : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      ((Scheme.Modules.restrictFunctor W.ι).obj
        ((naiveCotangentComplex f).homology (-1))).IsFiniteType := by
    intro x
    open Stacks.NaiveCotangentFinitePresentation in
    obtain ⟨U, V, hU, hV, hxV, hVU, M₁, M₀, δ, ψ, hψ, -, h₁, -, -⟩ :=
      exists_affine_quasiIso_associatedDouble_naiveCotangentComplex f x
    refine ⟨V, hxV, ?_⟩
    have hph : Functor.PreservesHomology (Scheme.Modules.restrictFunctor (V : X.Opens).ι) := by
      have := AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor (V : X.Opens).ι
      exact Functor.preservesHomology_of_preservesEpis_and_kernels _
    have e₁ := @Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso _ _ _ _ _ _ _ _
      (Scheme.Modules.restrictFunctor (V : X.Opens).ι) inferInstance hph
      (naiveCotangentComplex f) (-1) inferInstance inferInstance
    have hiso : IsIso (HomologicalComplex.homologyMap ψ (-1)) :=
      (quasiIsoAt_iff_isIso_homologyMap _ _).mp (hψ.quasiIsoAt (-1))
    let F := Stacks.AssociatedSheaf.associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace
      (Stacks.NaiveCotangentAffineIso.alpha (V := V))
    have e₂ : (Stacks.NaiveCotangentFinitePresentation.associatedDouble δ).homology (-1) ≅
        kernel (F.map δ) :=
      HomologicalComplex.doubleHomologyIsoKernel _
        (show (ComplexShape.up ℤ).Rel (-1) 0 by decide) (by decide)
    rw [show (Stacks.NaiveCotangentFinitePresentation.associatedDouble δ).X (-1) = F.obj M₁ from
      dite_eq_left rfl] at h₁
    have hk : (kernel (F.map δ)).IsFiniteType :=
      @Stacks.AlgebraicGeometry.CoherentOfFiniteType.isFiniteType_kernel_of_isQuasicoherent
        V.toScheme _ (F.obj M₁) (F.obj M₀) h₁
        (Stacks.AssociatedSheaf.isQuasicoherent_associatedSheafFunctor_obj
          V.toScheme.toRingedSpace (Stacks.NaiveCotangentAffineIso.alpha (V := V)) M₀) (F.map δ)
    exact AlgebraicGeometry.Modules.isFiniteType_of_iso
      (e₂.symm ≪≫ @asIso _ _ _ _ _ hiso ≪≫ e₁) hk
  choose W hxW hft using key
  refine AlgebraicGeometry.Modules.isFiniteType_of_restrict _ W (IsOpenCover.mk ?_) hft
  exact eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩

/-- **The cohomology sheaves of `NL_{X/Y}` are coherent** for `f` locally of finite type over a
locally Noetherian `Y`: in degree `0` it is `Ω_{X/Y}`, in degree `-1` it is quasi-coherent of
finite type on the locally Noetherian `X`, and in all other degrees it is zero. This is the
reading of [Stacks Project, Tag 0D0K] used in the proof of [Stacks Project, Tag 0DYA]. -/
theorem isCoherent_homology_naiveCotangentComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (i : ℤ) :
    ((naiveCotangentComplex f).homology i).IsCoherent := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  by_cases hneg : i = -1
  · subst hneg
    exact
      @Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
        X _ _ (isQuasicoherent_homology_naiveCotangentComplex f (-1))
        (isFiniteType_homology_naiveCotangentComplex_negOne f)
  by_cases hzero : i = 0
  · subst hzero
    exact ObjectProperty.prop_of_iso
      (P := fun N : SheafOfModules.{u} X.ringCatSheaf => N.IsCoherent)
      (naiveCotangentComplexHomologyZeroIso f).symm (Hom.isCoherent_relativeDifferentials f)
  exact ProperCoherentFiniteType.isCoherent_of_isZero
    (isZero_homology_naiveCotangentComplex f i hneg hzero)

end AlgebraicGeometry.Scheme

end
