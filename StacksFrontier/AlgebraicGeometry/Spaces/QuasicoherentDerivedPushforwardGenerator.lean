module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardAffineConservative
public import StacksFrontier.CategoryTheory.Triangulated.ConservativeRightAdjointGenerator
import StacksCore.Tactic.StacksAttribute

/-!
# Conservativity of `Rf_*` on `D_QCoh` and pulled back generators

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces and `E` a
generator of `D_QCoh(𝒪_Y)`. The following are equivalent (Stacks 0E4R): (1) for `K` in
`D_QCoh(𝒪_X)`, `Rf_*K = 0` if and only if `K = 0`; (2) `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`
reflects isomorphisms; (3) `Lf^*E` is a generator of `D_QCoh(𝒪_X)`. These conditions hold if `f`
is affine or an open immersion, and are stable under composition.

## Main results

* `AlgebraicGeometry.Space.tfae_reflectsIsomorphisms_quasicoherentDerivedPushforward`
* `AlgebraicGeometry.Space.isZero_quasicoherentDerivedPushforward_obj_iff_of_isAffineHom`
* `AlgebraicGeometry.Space.isZero_quasicoherentDerivedPushforward_obj_iff_of_isOpenImmersion`
* `AlgebraicGeometry.Space.isZero_quasicoherentDerivedPushforward_obj_iff_comp`

## References

* [Stacks Project, Tag 0E4R](https://stacks.math.columbia.edu/tag/0E4R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS}

/-- An object of `D_QCoh(𝒪_X)` is zero if and only if its underlying object of `D(𝒪_X)` is. -/
theorem isZero_quasicoherentDerivedCategory_iff
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    IsZero K ↔ IsZero K.obj :=
  ⟨fun h => (ObjectProperty.ι _).map_isZero h,
    fun h => IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) K h⟩

/-- **Stacks 0E4R.** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic
spaces and `E` a generator of `D_QCoh(𝒪_Y)`. The following are equivalent:
1. for `K` in `D_QCoh(𝒪_X)`, `Rf_*K = 0` if and only if `K = 0`;
2. `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` reflects isomorphisms;
3. `Lf^*E` is a generator of `D_QCoh(𝒪_X)`. -/
@[stacks 0E4R "the equivalence of (1), (2) and (3)"]
theorem tfae_reflectsIsomorphisms_quasicoherentDerivedPushforward (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (hE : ∀ K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2,
      IsZero K ↔ ∀ n : ℤ, Subsingleton (E⟦n⟧ ⟶ K)) :
    List.TFAE [∀ K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
        IsZero ((quasicoherentDerivedPushforward B S hS f hfqc hfqs).obj K) ↔ IsZero K,
      (quasicoherentDerivedPushforward B S hS f hfqc hfqs).ReflectsIsomorphisms,
      ∀ K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
        IsZero K ↔ ∀ n : ℤ, Subsingleton (((quasicoherentDerivedModulePullback f).obj E)⟦n⟧ ⟶ K)] :=
  Pretriangulated.tfae_reflectsIsomorphisms_of_adjunction
    (quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs) E hE

/-- **Stacks 0E4R, the case of an affine morphism.** For `f` affine, `Rf_*K = 0` if and only if
`K = 0`, for `K` in `D_QCoh(𝒪_X)`. -/
@[stacks 0E4R "the conditions hold if f is affine"]
theorem isZero_quasicoherentDerivedPushforward_obj_iff_of_isAffineHom (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hf : IsAffineHom B S hS f.hom) (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    IsZero ((quasicoherentDerivedPushforward B S hS f hfqc hfqs).obj K) ↔ IsZero K := by
  refine ⟨fun h => ?_, Functor.map_isZero _⟩
  rw [isZero_quasicoherentDerivedCategory_iff] at h ⊢
  exact isZero_of_isZero_derivedModulePushforward_of_isAffineHom B S hS f hf K.obj K.property h

/-- **Stacks 0E4R, the case of an open immersion.** For an open immersion `j`, `Rj_*K = 0` if and
only if `K = 0`: the restriction of `Rj_*K` to the open is `K`. -/
@[stacks 0E4R "the conditions hold if f is an open immersion"]
theorem isZero_quasicoherentDerivedPushforward_obj_iff_of_isOpenImmersion (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hf : IsOpenImmersion B S hS f.hom)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    IsZero ((quasicoherentDerivedPushforward B S hS f hfqc hfqs).obj K) ↔ IsZero K := by
  have het : IsEtale B S hS f.hom := isEtale_of_isOpenImmersion B S hS hf
  have : Mono f.hom := mono_of_isOpenImmersion B S hS f.hom hf
  have : Mono f := (ObjectProperty.ι _).mono_of_mono_map this
  have := isIso_etaleDerivedModuleAdjunction_counit_of_mono B S hS f het
  refine ⟨fun h => ?_, Functor.map_isZero _⟩
  rw [isZero_quasicoherentDerivedCategory_iff] at h ⊢
  exact ((Functor.map_isZero _ h).of_iso
    (asIso ((etaleDerivedModuleAdjunction B S hS f het).counit.app K.obj)).symm)

/-- **Stacks 0E4R, compositions.** If `Rf_*` and `Rg_*` detect zero objects of `D_QCoh`, then
so does `R(f ≫ g)_*`. -/
@[stacks 0E4R "the conditions are stable under composition"]
theorem isZero_quasicoherentDerivedPushforward_obj_iff_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hgqc : IsQuasiCompact B S hS g.hom) (hgqs : IsQuasiSeparated B S hS g.hom)
    (hfgqc : IsQuasiCompact B S hS (f ≫ g).hom) (hfgqs : IsQuasiSeparated B S hS (f ≫ g).hom)
    (hf : ∀ K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      IsZero ((quasicoherentDerivedPushforward B S hS f hfqc hfqs).obj K) ↔ IsZero K)
    (hg : ∀ K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2,
      IsZero ((quasicoherentDerivedPushforward B S hS g hgqc hgqs).obj K) ↔ IsZero K)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    IsZero ((quasicoherentDerivedPushforward B S hS (f ≫ g) hfgqc hfgqs).obj K) ↔ IsZero K := by
  have e := (quasicoherentDerivedPushforwardCompIso f g hfqc hfqs hgqc hgqs hfgqc hfgqs).app K
  exact ⟨fun h => (hf K).1 ((hg _).1 (h.of_iso e)), fun h => ((hg _).2 ((hf K).2 h)).of_iso e.symm⟩

end AlgebraicGeometry.Space

end
