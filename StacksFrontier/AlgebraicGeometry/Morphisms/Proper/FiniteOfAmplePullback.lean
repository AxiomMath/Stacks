module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.SectionRatioNoAmple.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.AmplePositivePower.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# A proper morphism along which a power of an ample module is a pullback is finite

Let `f : X ⟶ Y` be a proper morphism to a separated scheme, `𝓝` an ample invertible module on
`X`, and suppose that `𝓝^{⊗ m} ≅ f^*𝓜` for some `m ≥ 1` and some invertible module `𝓜` on `Y`.
Then `f` is finite. This is the finiteness step in the proof of [Stacks, Tag 0BFG], where `f` is
multiplication by `d` on an abelian variety and `𝓝^{⊗ d²} ≅ [d]^*𝓝` by [Stacks, Tag 0BFF].

The argument avoids curves in the fibres: the pullback of `𝓝^{⊗ m}` to a fibre `X_y` is ample,
by [Stacks, Tag 0892] (2), the inclusion of a fibre into `X` being affine, and it is trivial,
being pulled back from `Spec κ(y)`. So `𝒪_{X_y}` is ample and `X_y` is quasi-affine
([Stacks, Tag 01QE]). A quasi-affine scheme proper over a field is affine, hence finite over the
field, hence a finite set. So `f` has finite fibres, is locally quasi-finite, and, being proper,
is finite by Zariski's main theorem ([Stacks, Tag 02LS]).

## Main results

* `AlgebraicGeometry.isAffine_of_isQuasiAffine_of_universallyClosed`: a quasi-affine scheme
  universally closed over an affine scheme is affine.
* `AlgebraicGeometry.finite_of_isQuasiAffine_of_isProper`: a quasi-affine scheme proper over a
  field has finitely many points.
* `AlgebraicGeometry.finite_preimage_singleton_of_isAmple_tensorPowModule`: the fibres of `f`
  are finite.
* `AlgebraicGeometry.isFinite_of_isAmple_tensorPowModule`: `f` is finite.

## References

* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A quasi-affine scheme that is universally closed over an affine scheme is affine: the open
immersion into the spectrum of its global sections is universally closed, hence a closed
immersion. -/
theorem isAffine_of_isQuasiAffine_of_universallyClosed {F : Scheme.{u}} {R : CommRingCat.{u}}
    (g : F ⟶ Spec R) [F.IsQuasiAffine] [UniversallyClosed g] : IsAffine F := by
  have hnat : g ≫ (Spec R).toSpecΓ = F.toSpecΓ ≫ Spec.map g.appTop := Scheme.toSpecΓ_naturality g
  have : UniversallyClosed (F.toSpecΓ ≫ Spec.map g.appTop) := by rw [← hnat]; infer_instance
  have : UniversallyClosed F.toSpecΓ :=
    UniversallyClosed.of_comp_of_isSeparated F.toSpecΓ (Spec.map g.appTop)
  have : IsClosedImmersion F.toSpecΓ :=
    .of_isPreimmersion _ F.toSpecΓ.isClosedMap.isClosed_range
  exact isAffine_of_isAffineHom F.toSpecΓ

/-- A quasi-affine scheme proper over a field has finitely many points. -/
theorem finite_of_isQuasiAffine_of_isProper {F : Scheme.{u}} {K : Type u} [Field K]
    (g : F ⟶ Spec (.of K)) [F.IsQuasiAffine] [IsProper g] : Finite F := by
  have := isAffine_of_isQuasiAffine_of_universallyClosed g
  have : IsFinite g := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hsub : ∀ a b : Spec (.of K), a = b := fun a b =>
    PrimeSpectrum.ext ((@Ideal.eq_bot_of_prime _ _ a.asIdeal a.isPrime).trans
      (@Ideal.eq_bot_of_prime _ _ b.asIdeal b.isPrime).symm)
  by_cases hF : IsEmpty F
  · exact Finite.of_subsingleton
  obtain ⟨x⟩ := not_isEmpty_iff.mp hF
  have h := g.finite_preimage_singleton (g x)
  have : g ⁻¹' {g x} = Set.univ := Set.eq_univ_of_forall fun z => hsub _ _
  exact Set.finite_univ_iff.mp (this ▸ h)

/-- The inclusion of a fibre of a morphism to a separated scheme is affine. -/
theorem isAffineHom_fiberι [Y.IsSeparated] (f : X ⟶ Y) (y : Y) : IsAffineHom (f.fiberι y) := by
  have : IsAffineHom (Y.fromSpecResidueField y) :=
    IsAffineHom.of_comp (Y.fromSpecResidueField y) (terminal.from Y)
  exact isAffineHom_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).flip inferInstance

open Stacks.Ample in
/-- **A proper morphism is finite on fibres as soon as a positive power of an ample module is a
pullback.** Let `f : X ⟶ Y` be proper with `Y` separated, `N` an ample invertible module on `X`,
and suppose `N ^⊗ m ≅ f^*M` for an invertible module `M` on `Y` and some `m ≥ 1`. Then every
fibre of `f` is finite: the pullback of `N ^⊗ m` to the fibre `X_y` is ample (by
[Stacks, Tag 0892] (2), the fibre inclusion being affine) and trivial (being pulled back from
`Spec κ(y)`), so `X_y` is quasi-affine ([Stacks, Tag 01QE]); proper and quasi-affine over a field,
it is finite. -/
theorem finite_preimage_singleton_of_isAmple_tensorPowModule [Y.IsSeparated] (f : X ⟶ Y)
    [IsProper f] (N : X.Modules) [IsInvertibleModule X N] (hN : IsAmple X N)
    (M : Y.Modules) [IsInvertibleModule Y M] (m : ℕ) (hm : 1 ≤ m)
    (e : (Scheme.Modules.pullback f).obj M ≅ tensorPowModule X N (m : ℤ)) (y : Y) :
    (f ⁻¹' {y}).Finite := by
  have := isAffineHom_fiberι f y
  have : IsQuasiAffineHom (f.fiberι y) := isQuasiAffineHom_of_isAffineHom (f.fiberι y)
  have hNm : IsAmple X (tensorPowModule X N (m : ℤ)) :=
    Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple N m hm hN
  have h1 := Stacks.SectionRatioNoAmple.isAmple_modulePullback_of_isQuasiAffineHom (f.fiberι y)
    _ hNm
  have hMs : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ ‹IsInvertibleModule Y M›
  have hfM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj M) :=
    Stacks.RingedSpace.modulePullback_isInvertible _ M
  have : IsInvertibleModule X ((Scheme.Modules.pullback f).obj M) := hfM.toAlgebraicGeometry
  have hιfM : Stacks.SheafOfModules.IsInvertible (f.fiber y).presheaf (f.fiber y).ringCatIsSheaf
      ((RingedSpaceModuleAdjunction.modulePullback (f.fiberι y).toLRSHom.toShHom).obj
        ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj M)) :=
    Stacks.RingedSpace.modulePullback_isInvertible _ _
  have : IsInvertibleModule (f.fiber y)
      ((RingedSpaceModuleAdjunction.modulePullback (f.fiberι y).toLRSHom.toShHom).obj
        ((Scheme.Modules.pullback f).obj M)) := hιfM.toAlgebraicGeometry
  have h2 : IsAmple (f.fiber y)
      ((RingedSpaceModuleAdjunction.modulePullback (f.fiberι y).toLRSHom.toShHom).obj
        ((Scheme.Modules.pullback f).obj M)) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _
      ((RingedSpaceModuleAdjunction.modulePullback (f.fiberι y).toLRSHom.toShHom).mapIso
        e.symm)).mp h1
  -- the pullback of `f^*M` to the fibre is trivial
  have hsM : Stacks.SheafOfModules.IsInvertible (Spec (Y.residueField y)).presheaf
      (Spec (Y.residueField y)).ringCatIsSheaf
      ((RingedSpaceModuleAdjunction.modulePullback
        (Y.fromSpecResidueField y).toLRSHom.toShHom).obj M) :=
    Stacks.RingedSpace.modulePullback_isInvertible _ M
  have htriv : Stacks.SheafOfModules.IsTrivial (Spec (Y.residueField y)).presheaf
      (Spec (Y.residueField y)).ringCatIsSheaf
      ((RingedSpaceModuleAdjunction.modulePullback
        (Y.fromSpecResidueField y).toLRSHom.toShHom).obj M) :=
    have := hsM
    Stacks.PicardUFD.isTrivial_of_isInvertible_spec (Y.residueField y) _
  have hclass : Stacks.SheafOfModules.pullbackPicardClass (f.fiberι y)
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj M) hfM = 0 := by
    refine (Stacks.SheafOfModules.pullbackPicardClass_comp (f.fiberι y) f M hMs hfM).symm.trans ?_
    rw [Scheme.Hom.fiber_fac,
      Stacks.SheafOfModules.pullbackPicardClass_comp _ _ _ hMs hsM,
      Stacks.SheafOfModules.pullbackPicardClass_congr _ _ _ hsM
        (Stacks.SheafOfModules.isInvertible_unit _ _) htriv.some]
    exact Stacks.SheafOfModules.pullbackPicardClass_unit _ _
  obtain ⟨etriv⟩ := (Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff _ _ _).mp hclass
  have : (f.fiber y).IsQuasiAffine :=
    (Stacks.RelativeVeryAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule (f.fiber y) _
      etriv).mpr h2
  have : IsProper (f.fiberToSpecResidueField y) :=
    IsProper.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) ‹_›
  have : Finite (f.fiber y) := finite_of_isQuasiAffine_of_isProper
    (K := Y.residueField y) (f.fiberToSpecResidueField y)
  rw [← f.range_fiberι y]
  exact Set.finite_range _

open Stacks.Ample in
/-- **A proper morphism along which a positive power of an ample module is a pullback is
finite.** This is the finiteness step of the proof of [Stacks, Tag 0BFG]: the fibres are finite by
`AlgebraicGeometry.finite_preimage_singleton_of_isAmple_tensorPowModule`, so `f` is locally
quasi-finite, and a proper locally quasi-finite morphism is finite (Zariski's main theorem,
[Stacks, Tag 02LS]). -/
theorem isFinite_of_isAmple_tensorPowModule [Y.IsSeparated] (f : X ⟶ Y)
    [IsProper f] (N : X.Modules) [IsInvertibleModule X N] (hN : IsAmple X N)
    (M : Y.Modules) [IsInvertibleModule Y M] (m : ℕ) (hm : 1 ≤ m)
    (e : (Scheme.Modules.pullback f).obj M ≅ tensorPowModule X N (m : ℤ)) : IsFinite f := by
  have : LocallyQuasiFinite f := (locallyQuasiFinite_iff_finite_preimage_singleton).mpr
    (finite_preimage_singleton_of_isAmple_tensorPowModule f N hN M m hm e)
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite f).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
