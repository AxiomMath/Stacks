module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineSections
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingSliceSelfUnit
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectSectionsChart
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologyFlatExtension
public import StacksFrontier.RingTheory.Dualizing.RelativeHomothetyGeneral
public import StacksFrontier.RingTheory.Dualizing.RelativeHomothetySelfExt
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomothetyLocal
import StacksCore.Tactic.StacksAttribute

/-!
# The derived endomorphisms of a relative dualizing complex

Let `f : X ⟶ S` be flat and locally of finite presentation and let `(K, ξ)` be a relative
dualizing complex for `f` (Stacks 0E2T). Then the homothety `𝒪_X ⟶ R𝓗om_{𝒪_X}(K, K)` is an
isomorphism (Stacks 0E2V). The source's proof looks affine locally: over an affine open `U`
lying over an affine open `V`, the complex `RΓ(U, K)` is a relative dualizing complex for
`Γ(S, V) → Γ(X, U)` (Stacks 0E2U), its derived homothety is invertible (Stacks 0E2G), and the
comparison of Stacks 0A6H carries that to `R𝓗om(K|_U, K|_U) ≅ 𝒪_U`.

## Main results

* `Dualizing.isIso_derivedHomothety_of_isIso_relativeHomothety` — invertibility of the derived
  homothety `A ⟶ RHom_A(K, K)` passes from the adjunction of Stacks 0A63 to the chain-level
  adjunction the affine comparison of Stacks 0A6H is stated with, for `K` bounded below.
* `AlgebraicGeometry.isIso_derivedSheafHomothety_of_affineCharts` — the homothety
  `𝒪_X ⟶ R𝓗om(K, K)` of an object with quasi-coherent cohomology is invertible as soon as every
  point lies in an affine open `U` over which `RΓ(U, K)` is pseudo-coherent, bounded below and
  has invertible derived homothety.
* `Scheme.Hom.isIso_derivedSheafHomothety_of_isRelativeDualizingComplex_of_sections` — the
  homothety of `K` is invertible once `RΓ(U, K)` is a relative dualizing complex for
  `Γ(S, V) → Γ(X, U)` at every compatible pair of affine opens; this is the reduction of the
  source's proof, Stacks 0E2G supplying the algebraic case.
* `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex.isIso_derivedSheafHomothety` —
  **Stacks 0E2V**: for a relative dualizing complex `(K, ξ)`, `𝒪_X ⟶ R𝓗om(K, K)` is an
  isomorphism.

## References

* [Stacks Project, Lemma 48.28.3 (Tag 0E2V)](https://stacks.math.columbia.edu/tag/0E2V)
* [Stacks Project, Lemma 48.28.2 (Tag 0E2U)](https://stacks.math.columbia.edu/tag/0E2U)
* [Stacks Project, Lemma 47.27.7 (Tag 0E2G)](https://stacks.math.columbia.edu/tag/0E2G)
* [Stacks Project, Lemma 36.10.8 (Tag 0A6H)](https://stacks.math.columbia.edu/tag/0A6H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
open Opposite

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Dualizing

open StacksDraft.DerivedHom

variable (A : Type u) [CommRing A]

/-- **The derived homothety in the two models of `RHom_A`.** For `K` bounded below in `D(A)`, if
the derived homothety `A ⟶ RHom_A(K, K)` of the adjunction of Stacks 0A63 is an isomorphism,
then so is the derived homothety of the chain-level adjunction
`StacksDraft.DerivedHom.derivedHomAdjunction`.

Invertibility at the first adjunction says that scalars exhaust `End_{D(A)}(K)` freely and that
`K` has no morphism to a nonzero shift of itself; on a bounded below injective model `J` of `K`
this is the rank-one criterion for the homothety of `J`, which gives invertibility at the
second adjunction. -/
theorem isIso_derivedHomothety_of_isIso_relativeHomothety (K : DerivedCategory (ModuleCat.{u} A))
    (a : ℤ) [K.IsGE a] [IsIso (relativeHomothety A K)] :
    IsIso (derivedHomothety
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (StacksDraft.DerivedHom.Model.Complex A)))
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).tensorUnitLeft K) := by
  have hbij := bijective_smul_id_of_isIso_relativeHomothety A K
  have hvan := subsingleton_shift_of_isIso_relativeHomothety A K
  obtain ⟨P, hP, ⟨eP⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K a
  obtain ⟨Rs, -, hR⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a P
  let J := Rs.cocomplex
  have : J.IsKInjective := CochainComplex.isKInjective_of_injective J a
  let e : K ≅ DerivedCategory.Q.obj J := eP ≪≫ asIso (DerivedCategory.Q.map Rs.ι)
  have hbij' : Function.Bijective (LinearMap.toSpanSingleton A (End K) 1) := by
    convert End.homEquiv.symm.bijective.comp hbij using 1
    funext r
    ext
    simp [End.smul_asHom]
  let e₀ : End K ≃ₗ[A] A :=
    (LinearEquiv.ofBijective (LinearMap.toSpanSingleton A (End K) 1) hbij').symm
  have hJ : QuasiIso (homothety J) := by
    refine quasiIso_homothety_of_rankOne.{u, 0} J
      ((homologyZeroEndLinearEquiv J).trans ((endLinearEquivOfIso e.symm).trans e₀))
      fun n hn => ?_
    refine isZero_homology_homComplexR_of_subsingleton.{u, 0} J a n ?_
    have := hvan n hn
    exact Equiv.subsingleton
      (Iso.homCongr e ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).mapIso e)).symm
  have : J.IsStrictlyGE a := hR
  have : ∀ i : ℤ, Injective (J.X i) := Rs.injective
  exact isIso_derivedHomothety_of_injectiveRepresentative _ K J a e.symm hJ

end Dualizing

namespace AlgebraicGeometry

/-- **The homothety of `K` is invertible when it is so on affine charts.** Let `K` be an object
of `D(𝒪_X)` with quasi-coherent cohomology sheaves. If every point of `X` lies in an affine open
`U` such that `RΓ(U, K)` is pseudo-coherent and bounded below and its derived homothety
`Γ(X, U) ⟶ RHom(RΓ(U, K), RΓ(U, K))` is an isomorphism, then `𝒪_X ⟶ R𝓗om_{𝒪_X}(K, K)` is an
isomorphism.

On an affine open `K|_U` is the complex associated to `RΓ(U, K)` (Stacks 06Z0), so the
comparison of Stacks 0A6H (3)(a) identifies `R𝓗om(K|_U, K|_U)` with `𝒪_U`; invertibility of the
homothety is local on `X`. -/
theorem isIso_derivedSheafHomothety_of_affineCharts {X : Scheme.{u}}
    (K : DerivedCategory X.Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : IsAffineOpen U), x ∈ U ∧
      StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedSectionsUnbounded X U).obj K) ∧
      (DerivedCategory.TStructure.t).plus ((derivedSectionsUnbounded X U).obj K) ∧
      IsIso (Dualizing.relativeHomothety Γ(X, U) ((derivedSectionsUnbounded X U).obj K))) :
    IsIso (Stacks.SheafOfModules.derivedSheafHomothety X.sheaf K) := by
  choose U hU hx hpc hplus hh using h
  have hY : (Opens.grothendieckTopology X).CoversTop U :=
    (Opens.coversTop_iff _ _).2 (TopologicalSpace.IsOpenCover.mk
      (eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩))
  refine Stacks.SheafOfModules.isIso_derivedSheafHomothety_of_iso_unit X.sheaf K hY
    fun x => ?_
  obtain ⟨M, ⟨e₁⟩, ⟨e₂⟩⟩ := affineDerivedSectionsPresentation K hqc (U x) (hU x)
  obtain ⟨a, ha⟩ := hplus x
  have : M.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso e₂.symm a
  have hpcM : StacksDraft.PseudoCoherence.IsPseudoCoherent M :=
    StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso (hpc x) e₂.symm
  have : IsIso (Dualizing.relativeHomothety Γ(X, U x) M) :=
    (Dualizing.isIso_relativeHomothety_iff_of_iso Γ(X, U x) e₂).2 (hh x)
  have hhM := Dualizing.isIso_derivedHomothety_of_isIso_relativeHomothety Γ(X, U x) M a
  let r : tilde.functor Γ(X, U x) ⋙ Scheme.Modules.pushforward (hU x).isoSpec.inv ≅
      tilde.functor Γ(X, U x) ⋙ Scheme.Modules.restrictFunctor (hU x).isoSpec.hom :=
    Functor.isoWhiskerLeft _
      (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv
        (hU x).isoSpec).symm
  let i := (Stacks.SheafOfModules.derivedOverFunctorEquiv (U x)).app K ≪≫ e₁ ≪≫
    (RingTheory.TorIndependence.mapDerivedCategoryCompIso _ _ _ r).app M
  exact Stacks.Duality.nonempty_derivedSheafHom_restrictD_self_iso_unit (U x) (hU x) hpcM
    ⟨a, inferInstance⟩ hhM K i

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The reduction of Stacks 0E2V to the algebraic case.** Let `f : X ⟶ S` be flat and locally
of finite presentation and let `K` be an object of `D(𝒪_X)` with quasi-coherent cohomology such
that, for every affine open `V ⊆ S` and every affine open `U ⊆ f⁻¹(V)`, the complex `RΓ(U, K)` is
a relative dualizing complex for the chart ring map `Γ(S, V) → Γ(X, U)` (Stacks 0E2C). Then
`𝒪_X ⟶ R𝓗om_{𝒪_X}(K, K)` is an isomorphism.

Over each chart the derived homothety of `RΓ(U, K)` is invertible by Stacks 0E2G, and
`RΓ(U, K)`, being perfect relative to `Γ(S, V)`, is pseudo-coherent and bounded. -/
theorem isIso_derivedSheafHomothety_of_isRelativeDualizingComplex_of_sections [Flat f]
    [LocallyOfFinitePresentation f] (K : DerivedCategory X.Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
      (hUV : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      letI : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
      letI : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
        algebraFinitePresentation_appLE f hV hU hUV rfl
      Dualizing.IsRelativeDualizingComplex Γ(S, V) Γ(X, U)
        ((derivedSectionsUnbounded X U).obj K)) :
    IsIso (Stacks.SheafOfModules.derivedSheafHomothety X.sheaf K) := by
  refine isIso_derivedSheafHomothety_of_affineCharts K hqc fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := f.base x) (U := ⊤) (by simp)
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V) hxV
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
  let : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
    algebraFinitePresentation_appLE f hV hU hUV rfl
  have hK := h U hU V hV hUV
  obtain ⟨P, a, b, hGE, hLE, -, -, ⟨eP⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation _ _ _
      _).1 hK.relativelyPerfect
  exact ⟨U, hU, hxU, hK.relativelyPerfect.1,
    ⟨a, DerivedCategory.TStructure.t.isGE_of_iso eP.symm a⟩,
    Dualizing.isIso_relativeHomothety_of_isRelativeDualizingComplex _ hK⟩

end Scheme.Hom

namespace Scheme.Hom.IsRelativeDualizingComplex

variable {X S : Scheme.{u}} {f : X ⟶ S} [Flat f] [LocallyOfFinitePresentation f]

/-- **Stacks 0E2V.** Let `f : X ⟶ S` be flat and locally of finite presentation and let `(K, ξ)`
be a relative dualizing complex for `f` (Stacks 0E2T), relative to an open `W ⊆ X ×_S X` through
which the relative diagonal factors as a closed immersion. Then the homothety
`𝒪_X ⟶ R𝓗om_{𝒪_X}(K, K)` is an isomorphism.

`S`-perfectness is read at the derived tensor product of Stacks 06YU on the open subspaces of
`(X, f⁻¹𝒪_S)`, as in Stacks 0DI2 and Stacks 0E2U. The proof is the source's: on every compatible
pair of affine opens `RΓ(U, K)` is a relative dualizing complex for `Γ(S, V) → Γ(X, U)` by
Stacks 0E2U, and the algebraic case is Stacks 0E2G. -/
@[stacks 0E2V]
theorem isIso_derivedSheafHomothety {D : DiagonalOpen f}
    {K : DerivedCategory X.Modules} {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ) :
    IsIso (Stacks.SheafOfModules.derivedSheafHomothety X.sheaf K) :=
  isIso_derivedSheafHomothety_of_isRelativeDualizingComplex_of_sections f K
    (isQuasicoherentDerived_of_isPseudoCoherent X K hK.isPerfectRelativeTo.1)
    fun _ hU _ hV hUV => hK.isRelativeDualizingComplex_derivedSections hU hV hUV

end Scheme.Hom.IsRelativeDualizingComplex

end AlgebraicGeometry

end
