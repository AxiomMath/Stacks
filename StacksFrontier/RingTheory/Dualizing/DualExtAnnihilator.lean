module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.Dualizing.DualExtDepthDimension
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityExt
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian

/-!
# The dual Ext modules and local cohomology have the same annihilator

Let `(A, 𝔪)` be a Noetherian local ring with a normalized dualizing complex `ω_A^•`, and let
`M` be a finite `A`-module. Write

`Eⁱ = Ext_A^{-i}(M, ω_A^•)` and `Hⁱ_𝔪(M)`

for the dual Ext modules and the local cohomology modules of `M` at the closed point. These
two families of modules are not isomorphic — one is finite and the other is almost never so —
but they have the same annihilator in every degree.

The reason is local duality: the `𝔪`-adic completion of `Eⁱ` is the Matlis dual
`Hom_A(Hⁱ_𝔪(M), E)` of `Hⁱ_𝔪(M)`, where `E` is an injective hull of the residue field.
Completion changes nothing on the left, because `Eⁱ` is a finite module and `A → A^∧` is
faithfully flat, so `Eⁱ` and its completion are annihilated by the same elements. Nothing is
lost on the right either: a module and its Matlis dual have the same annihilator, because an
element `r` failing to annihilate `N` produces a nonzero cyclic quotient of `rN` mapping to
the residue field, and injectivity of `E` extends that map to `N`.

## Main results

* `Dualizing.annihilator_moduleExtInto_eq_annihilator_localCohomology` — the annihilators of
  `Eⁱ` and of `Hⁱ_𝔪(M)` agree.

## Implementation notes

The module `Eⁱ` is `Dualizing.moduleExtInto M ω (-i)`, the spelling used throughout the
surrounding files, and local cohomology at the closed point is
`Stacks.LocalCohomology.localCohomologyWithSupportIn` at the closed subset
`V(𝔪) ⊆ Spec(A)`. Local duality is available in the second model of local cohomology, the
right adjoint `RΓ_{V(𝔪)}` of the inclusion of the objects with `𝔪`-power-torsion cohomology;
over a Noetherian ring the two models agree, which is
`Stacks.LocalCohomology.isIso_compareSectionsWithSupportLocalCohomology_app`.

The two steps of the argument are isolated as statements about an abstract module:
completion does not change the annihilator of a finite module over a Noetherian local ring,
and Matlis duality against any injective module receiving the residue field does not change
the annihilator of an arbitrary module.

## References

* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK)
* [Stacks Project, Tag 08Z9](https://stacks.math.columbia.edu/tag/08Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w x

namespace Dualizing

/-- A finite module over a Noetherian local ring has the same annihilator as its `𝔪`-adic
completion. Multiplication by a ring element commutes with completion, so it vanishes on the
completion as soon as it vanishes on the module; conversely the completion map is injective,
by the Krull intersection theorem. -/
private theorem annihilator_adicCompletion_eq
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    Module.annihilator R N =
      Module.annihilator R (AdicCompletion (IsLocalRing.maximalIdeal R) N) := by
  let I := IsLocalRing.maximalIdeal R
  have hmap (a : R) :
      (AdicCompletion.map I (LinearMap.lsmul R N a)).restrictScalars R =
        LinearMap.lsmul R (AdicCompletion I N) a := by
    apply AdicCompletion.map_ext''
    ext x
    simp [AdicCompletion.val_smul_apply]
  ext r
  rw [Module.mem_annihilator, Module.mem_annihilator]
  constructor
  · intro h x
    have hf : LinearMap.lsmul R N r = 0 := LinearMap.ext h
    have hact : LinearMap.lsmul R (AdicCompletion I N) r = 0 := by
      rw [← hmap r, hf, AdicCompletion.map_zero]
      rfl
    exact LinearMap.congr_fun hact x
  · intro h x
    have hz : (AdicCompletion.map I (LinearMap.lsmul R N r)).restrictScalars R = 0 := by
      rw [hmap r]
      exact LinearMap.ext h
    apply AdicCompletion.of_injective I N
    simpa [AdicCompletion.map_of] using LinearMap.congr_fun hz (AdicCompletion.of I N x)

/-- Matlis duality does not change the annihilator. If `E` is an injective module over a local
ring `R` receiving the residue field injectively, then `N` and `Hom_R(N, E)` have the same
annihilator, for every `R`-module `N`. An element `r` not annihilating `N` gives a nonzero
element `r • x`, whose cyclic submodule surjects onto the residue field; the resulting map to
`E` extends to `N` by injectivity, and the extension is not killed by `r`. -/
private theorem annihilator_eq_linearDual_of_injectiveResidue
    {R : Type u} [CommRing R] [IsLocalRing R]
    {N E : Type w} [AddCommGroup N] [Module R N]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    (ι : ULift.{x} (IsLocalRing.ResidueField R) →ₗ[R] E)
    (hι : Function.Injective ι) :
    Module.annihilator R N = Module.annihilator R (N →ₗ[R] E) := by
  classical
  ext r
  rw [Module.mem_annihilator, Module.mem_annihilator]
  constructor
  · intro hr φ
    ext x
    rw [LinearMap.smul_apply, ← map_smul, hr x, map_zero, LinearMap.zero_apply]
  · intro hr
    by_contra hrN
    obtain ⟨x, hx⟩ := not_forall.mp hrN
    let y : N := r • x
    have hy : y ≠ 0 := hx
    let f : R →ₗ[R] N := LinearMap.lsmul R N |>.flip y
    have hf1 : f 1 ≠ 0 := by simpa [f] using hy
    let J : Ideal R := LinearMap.ker f
    have hJ : J ≤ IsLocalRing.maximalIdeal R := by
      intro a ha
      by_contra ham
      have hu : IsUnit a := IsLocalRing.notMem_maximalIdeal.mp ham
      have haf : a • y = 0 := by simpa [f, J, LinearMap.mem_ker] using ha
      exact hy ((IsUnit.smul_eq_zero hu).mp haf)
    let q : R ⧸ J →ₗ[R] IsLocalRing.ResidueField R :=
      Submodule.liftQ J (Algebra.linearMap R (IsLocalRing.ResidueField R)) (by
        intro a ha
        change algebraMap R (IsLocalRing.ResidueField R) a = 0
        rw [IsLocalRing.ResidueField.algebraMap_eq]
        exact (IsLocalRing.residue_eq_zero_iff a).2 (hJ ha))
    let g : LinearMap.range f →ₗ[R] E :=
      ι.comp (ULift.moduleEquiv.symm.toLinearMap.comp
        (q.comp f.quotKerEquivRange.symm.toLinearMap))
    obtain ⟨φ, hφ⟩ := Module.Injective.out (R := R)
      (LinearMap.range f).subtype (LinearMap.range f).subtype_injective g
    let z : LinearMap.range f := ⟨f 1, ⟨1, rfl⟩⟩
    have hquot : f.quotKerEquivRange.symm z = (LinearMap.ker f).mkQ 1 := by
      dsimp [z]
      exact f.quotKerEquivRange_symm_apply_image 1
        (show f 1 ∈ LinearMap.range f from ⟨1, rfl⟩)
    have hq1 : q ((LinearMap.ker f).mkQ 1) = 1 := by
      change Submodule.liftQ J (Algebra.linearMap R (IsLocalRing.ResidueField R)) _
        (Submodule.Quotient.mk 1) = 1
      rw [Submodule.liftQ_apply]
      simp
    have hg1 : g z = ι (ULift.up (1 : IsLocalRing.ResidueField R)) := by
      change ι (ULift.moduleEquiv.symm (q (f.quotKerEquivRange.symm z))) = _
      rw [hquot, hq1]
      simp
    have hne : ι (ULift.up (1 : IsLocalRing.ResidueField R)) ≠ 0 := fun h =>
      one_ne_zero (congrArg ULift.down (hι (h.trans (map_zero ι).symm)))
    have hzero : φ (r • x) = 0 := by simpa using LinearMap.congr_fun (hr φ) x
    have : φ (f 1) = g z := hφ z
    rw [show f 1 = y by simp [f], hg1] at this
    exact hne (this.symm.trans hzero)

/-- **A finite module placed in degree zero has finite cohomology in every degree**: the module
itself in degree zero, the zero module everywhere else. No finiteness of the ring is needed. -/
public theorem finite_homology_single {A : Type u} [CommRing A]
    (M₀ : ModuleCat.{w} A) [Module.Finite A (M₀ : Type w)] (j : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) j).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj M₀)) := by
  let C := ModuleCat.{w} A
  by_cases hj : j = 0
  · subst j
    let : Module.Finite A (↑((𝟭 C).obj M₀)) :=
      inferInstanceAs (Module.Finite A (M₀ : Type w))
    let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M₀
    exact Module.Finite.of_surjective e.inv.hom fun x => ⟨e.hom.hom x, by simp⟩
  · let X := (CochainComplex.singleFunctor C 0).obj M₀
    have hz : IsZero ((DerivedCategory.homologyFunctor C j).obj
        ((DerivedCategory.singleFunctor C 0).obj M₀)) := by
      let e₁ := (DerivedCategory.homologyFunctorFactors C j).app X
      let e₀ := (DerivedCategory.homologyFunctor C j).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app M₀)
      exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M₀ j
        hj).of_iso (e₀ ≪≫ e₁)
    let : Subsingleton ↑((DerivedCategory.homologyFunctor C j).obj
        ((DerivedCategory.singleFunctor C 0).obj M₀)) :=
      ModuleCat.subsingleton_of_isZero hz
    exact Module.Finite.of_surjective (0 : A →ₗ[A]
      ↑((DerivedCategory.homologyFunctor C j).obj ((DerivedCategory.singleFunctor C 0).obj M₀)))
      fun x => ⟨0, Subsingleton.elim _ _⟩

/-- **Stacks Project, Tag 0DWZ, part (5).** Let `(A, 𝔪)` be a Noetherian local ring with a
normalized dualizing complex `ω`, and let `M` be a finite `A`-module. Then the dual Ext module
`Eⁱ = Ext_A^{-i}(M, ω)` and the local cohomology module `Hⁱ_𝔪(M)` have the same annihilator.

Local duality identifies the `𝔪`-adic completion of `Eⁱ` with the module of `A`-linear maps
from `Hⁱ_𝔪(M)` to an injective hull of the residue field. Neither completing a finite module
nor passing to the Matlis dual changes the annihilator, so the two annihilators agree. -/
@[stacks 0DWZ "part (5): Ext^{-i}(M, ω) and H^i_m(M) have the same annihilator"]
theorem annihilator_moduleExtInto_eq_annihilator_localCohomology
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K) (i : ℤ) :
    Module.annihilator A (moduleExtInto M K (-i)) =
      Module.annihilator A
        (Stacks.LocalCohomology.localCohomologyWithSupportIn A
          (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal A : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) := by
  classical
  have hmFG : (IsLocalRing.maximalIdeal A).FG := IsNoetherian.noetherian _
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hmFG
  let M₀ : ModuleCat.{u} A := ModuleCat.of A M
  let K₀ : DerivedCategory (ModuleCat.{u} A) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M₀
  let k₀ : ModuleCat.{u} A := (ModuleCat.uliftFunctor.{u} A).obj
    (ModuleCat.of A (IsLocalRing.ResidueField A))
  obtain ⟨E, e, heMono, heHull⟩ := Module.exists_isInjectiveHull A k₀
  let : Mono e := heMono
  have heHull' : Module.IsInjectiveHull e := heHull
  obtain ⟨eDual⟩ :=
    LocalDuality.nonempty_adicCompletion_ext_linearEquiv_linearMap_localCohomology
      A f hf K hK K₀ (fun j => finite_homology_single (ModuleCat.of A M) j) e heHull' i
  -- The two models of local cohomology agree over a Noetherian ring.
  have := Stacks.LocalCohomology.isIso_compareSectionsWithSupportLocalCohomology_app.{u, u}
    A (IsLocalRing.maximalIdeal A) hmFG K₀
  let eC := asIso ((Stacks.LocalCohomology.compareSectionsWithSupportLocalCohomology.{u, u}
    A (IsLocalRing.maximalIdeal A) hmFG).app K₀)
  let eL := ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso eC).toLinearEquiv
  -- The annihilator is unchanged by completion, and by Matlis duality.
  have : Module.Finite A (DerivedCategory.Ext K₀ K (-i)) :=
    moduleExtInto_finite (A := A) (M := M) K hK i
  have : Module.Injective A (↑E) := (Module.injective_iff_injective_object A E).mpr heHull'.1
  calc
    Module.annihilator A (moduleExtInto M K (-i))
        = Module.annihilator A
          (AdicCompletion (IsLocalRing.maximalIdeal A) (DerivedCategory.Ext K₀ K (-i))) :=
        annihilator_adicCompletion_eq _
    _ = Module.annihilator A
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            ((derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A)
                (IsNoetherian.noetherian _)).ι.obj
              ((localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
                (IsNoetherian.noetherian _)).obj K₀)) →ₗ[A] ↑E) := eDual.annihilator_eq
    _ = Module.annihilator A
          (Stacks.LocalCohomology.localCohomologyWithSupportIn A
            (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal A : Set A)) K₀ i →ₗ[A] ↑E) :=
        (LinearEquiv.arrowCongr eL (LinearEquiv.refl A (↑E : Type u))).annihilator_eq.symm
    _ = Module.annihilator A
          (Stacks.LocalCohomology.localCohomologyWithSupportIn A
            (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal A : Set A)) K₀ i) :=
        (annihilator_eq_linearDual_of_injectiveResidue e.hom
          ((ModuleCat.mono_iff_injective e).mp heMono)).symm

end Dualizing

end
