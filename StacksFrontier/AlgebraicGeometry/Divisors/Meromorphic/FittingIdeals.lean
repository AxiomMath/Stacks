module

public import Mathlib.Algebra.Module.Presentation.Finite
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.RingTheory.Fitting.Basic
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus

/-!
# Fitting ideal sheaves

The Fitting ideals of the modules of sections of a quasi-coherent module of finite type on a
scheme are compatible with localization, hence assemble into a quasi-coherent ideal sheaf. That
ideal sheaf commutes with arbitrary base change, and for a finitely presented module it is of
finite type.

## Main definitions

* `AlgebraicGeometry.fittingIdeal`: the ℤ-indexed Fitting ideal sheaf.
* `AlgebraicGeometry.fittingIdealOfNat`: its ℕ-indexed specialization.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`: finite type for a quasi-coherent
  ideal sheaf.

## Main results

* `AlgebraicGeometry.fittingIdeal_ideal`: on an affine open the ideal sheaf is the
  module-theoretic Fitting ideal of the sections there.
* `AlgebraicGeometry.fittingIdeal_comap`: Fitting ideal sheaves commute with base change.
* `AlgebraicGeometry.fittingIdeal_isFiniteType`: for a finitely presented module the Fitting
  ideal sheaves are of finite type.

## Implementation notes

The module-theoretic Fitting ideal is the existing `fittingIdeal` for finite modules. On opens
where the sections are not finite the defining family is set to zero; this does not affect
finite-type quasi-coherent modules on affine opens. The affine-open characterization records
that, under the hypotheses of the source, `Scheme.IdealSheafData.ofIdeals` recovers the
prescribed family rather than merely the largest ideal sheaf below it. Integer indexing also
covers the conventional negative Fitting ideals, and the ℕ-indexed version is defined as the
specialization rather than re-derived, so the base-change and finite-type statements apply to
one and the same ideal sheaf. The left-hand side of the base-change result uses
`Scheme.IdealSheafData.comap`, Mathlib's scheme-theoretic inverse-image ideal.

## References

* [Stacks Project, Tag 0C3D](https://stacks.math.columbia.edu/tag/0C3D)
* [Stacks Project, Tag 0C3E](https://stacks.math.columbia.edu/tag/0C3E)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

private lemma moduleFittingIdeal_eq_of_linearEquiv
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : M ≃ₗ[R] N) (k : ℤ) :
    _root_.fittingIdeal (R := R) (M := M) k = _root_.fittingIdeal (R := R) (M := N) k := by
  by_cases hk : k < 0
  · simp [_root_.fittingIdeal, hk]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hk)
    exact fittingIdeal_eq_of_linearEquiv e n

@[sga "7 VI 5.1"]
private lemma moduleFittingIdeal_baseChange
    {R M S : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [CommRing S] [Algebra R S] (k : ℤ) :
    _root_.fittingIdeal (R := S) (M := TensorProduct R S M) k =
      Ideal.map (algebraMap R S) (_root_.fittingIdeal (R := R) (M := M) k) := by
  by_cases hk : k < 0
  · simp [_root_.fittingIdeal, hk]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hk)
    exact (fittingIdeal_basic_properties.{u, u, u, u} (R := R) (M := M)).2.2.1 S n

/-- The Fitting ideal commutes with base change along an isomorphism with an extension of
scalars. -/
private lemma moduleFittingIdeal_map_eq_of_extendScalars_iso {R S : CommRingCat.{u}} (α : R ⟶ S)
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module S N] [Module.Finite S N]
    (e : (ModuleCat.extendScalars α.hom).obj (ModuleCat.of R M) ≅ ModuleCat.of S N) (k : ℤ) :
    Ideal.map α.hom (_root_.fittingIdeal (R := R) (M := M) k) =
      _root_.fittingIdeal (R := S) (M := N) k := by
  let : Algebra R S := α.hom.toAlgebra
  let ε : TensorProduct R S M ≃ₗ[S] N :=
    LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)
  exact (moduleFittingIdeal_baseChange k).symm.trans (moduleFittingIdeal_eq_of_linearEquiv ε k)

private noncomputable def moduleSectionsIsoOfIso {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) (U : X.Opens) : Γ(F, U) ≃ₗ[Γ(X, U)] Γ(G, U) := by
  let φ : Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U) := (e.hom.val.app (Opposite.op U)).hom
  let ψ : Γ(G, U) →ₗ[Γ(X, U)] Γ(F, U) := (e.inv.val.app (Opposite.op U)).hom
  have hleft : ψ.comp φ = LinearMap.id := by
    convert congrArg (fun α : F ⟶ F => (α.val.app (Opposite.op U)).hom)
      e.hom_inv_id using 1 <;> rfl
  have hright : φ.comp ψ = LinearMap.id := by
    convert congrArg (fun α : G ⟶ G => (α.val.app (Opposite.op U)).hom)
      e.inv_hom_id using 1 <;> rfl
  exact LinearEquiv.ofLinearMap φ ψ hright hleft

private lemma moduleFittingIdeal_map_basicOpen {X : Scheme.{u}} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (U : X.affineOpens) (s : Γ(X, U.1))
    [Module.Finite Γ(X, U.1) Γ(F, U.1)]
    [Module.Finite Γ(X, (X.affineBasicOpen s).1) Γ(F, (X.affineBasicOpen s).1)] (k : ℤ) :
    Ideal.map (((𝟙 X : X ⟶ X).appLE U.1 (X.affineBasicOpen s).1
      (X.basicOpen_le s)).hom)
        (_root_.fittingIdeal (M := Γ(F, U.1)) k) =
      _root_.fittingIdeal (M := Γ(F, (X.affineBasicOpen s).1)) k := by
  classical
  let i : X ⟶ X := 𝟙 X
  let V : X.affineOpens := X.affineBasicOpen s
  have : Module.Finite Γ(X, V.1) Γ(F, V.1) := moduleFinite_sections_on_affine F V.1 V.2
  exact moduleFittingIdeal_map_eq_of_extendScalars_iso (N := Γ(F, V.1))
    (i.appLE U.1 V.1 (X.basicOpen_le s))
    (affinePullbackSectionsBaseChangeIso i F U.2 V.2 (X.basicOpen_le s) ≪≫
      (moduleSectionsIsoOfIso ((Scheme.Modules.pullbackId X).app F) V.1).toModuleIso) k

/-- The `k`-th Fitting ideal sheaf of a sheaf of modules on a scheme. On
affine opens it is determined by the Fitting ideals of the modules of
sections. -/
@[sga "7 VI 5.2" "more general", sga "7 VI 5.5" "special case"]
noncomputable def fittingIdeal {X : Scheme.{u}} (F : X.Modules) (k : ℤ) :
    X.IdealSheafData := by
  classical
  exact Scheme.IdealSheafData.ofIdeals fun U ↦
    if h : Module.Finite Γ(X, U.1) Γ(F, U.1) then
      haveI := h
      _root_.fittingIdeal (M := Γ(F, U.1)) k
    else ⊥

/-- On every affine open, the Fitting ideal sheaf of a finite type
quasi-coherent module is the module-theoretic Fitting ideal of its sections. -/
theorem fittingIdeal_ideal {X : Scheme.{u}} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (k : ℤ) (U : X.affineOpens)
    [Module.Finite Γ(X, U.1) Γ(F, U.1)] :
    (fittingIdeal F k).ideal U =
      _root_.fittingIdeal (M := Γ(F, U.1)) k := by
  classical
  let A : ∀ V : X.affineOpens, Ideal Γ(X, V.1) := fun V ↦
    if h : Module.Finite Γ(X, V.1) Γ(F, V.1) then
      have := h
      _root_.fittingIdeal (M := Γ(F, V.1)) k
    else ⊥
  have hmap (V : X.affineOpens) (s : Γ(X, V.1)) :
      (A V).map (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom =
        A (X.affineBasicOpen s) := by
    have hV : Module.Finite Γ(X, V.1) Γ(F, V.1) := moduleFinite_sections_on_affine F V.1 V.2
    have hD : Module.Finite Γ(X, (X.affineBasicOpen s).1) Γ(F, (X.affineBasicOpen s).1) :=
      moduleFinite_sections_on_affine F _ (X.affineBasicOpen s).2
    simp only [A]
    rw [dite_eq_left hV, dite_eq_left hD]
    exact moduleFittingIdeal_map_basicOpen F V s k
  let J : X.IdealSheafData :=
    { ideal := A
      map_ideal_basicOpen := hmap }
  change (Scheme.IdealSheafData.ofIdeals J.ideal).ideal U = _
  rw [Scheme.IdealSheafData.ofIdeals_ideal J]
  exact dite_eq_left ‹Module.Finite Γ(X, U.1) Γ(F, U.1)›

/-- Isomorphic sheaves of modules on a scheme have the same Fitting ideal sheaves: the Fitting
ideal sheaf is an invariant of the isomorphism class of the module. -/
theorem fittingIdeal_eq_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) (k : ℤ) :
    fittingIdeal F k = fittingIdeal G k := by
  classical
  unfold AlgebraicGeometry.fittingIdeal
  congr 1
  funext U
  let ε : Γ(F, U.1) ≃ₗ[Γ(X, U.1)] Γ(G, U.1) := moduleSectionsIsoOfIso e U.1
  by_cases hF : Module.Finite Γ(X, U.1) Γ(F, U.1)
  · have hG : Module.Finite Γ(X, U.1) Γ(G, U.1) :=
      Module.Finite.of_surjective ε.toLinearMap ε.surjective
    simp only [dite_eq_left hF, dite_eq_left hG]
    exact moduleFittingIdeal_eq_of_linearEquiv ε k
  · have hG : ¬ Module.Finite Γ(X, U.1) Γ(G, U.1) := fun hG =>
      hF (Module.Finite.of_surjective ε.symm.toLinearMap ε.symm.surjective)
    simp only [dite_eq_right hF, dite_eq_right hG]

/-- **Stacks Project, Tag 0C3D.** Fitting ideal sheaves of finite type
quasi-coherent modules commute with arbitrary base change. -/
@[stacks 0C3D]
theorem fittingIdeal_comap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Y.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (k : ℤ) :
    (fittingIdeal F k).comap f =
      fittingIdeal ((Scheme.Modules.pullback f).obj F) k := by
  classical
  let G := (Scheme.Modules.pullback f).obj F
  have : G.IsFiniteType := SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom F
  have : G.IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent X.toRingedSpace Y.toRingedSpace
      f.toLRSHom.toShHom F ‹F.IsQuasicoherent›
  let ι := Σ U : Y.affineOpens, {V : X.affineOpens // (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)}
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i : ι ↦ i.2.1) ?_ ?_
  · refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ f ⁻¹ᵁ U from hxU) (f ⁻¹ᵁ U).isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨⟨U, hU⟩, ⟨V, hV⟩, hVU⟩, hxV⟩
  · rintro ⟨U, V, hVU⟩
    change ((fittingIdeal F k).comap f).ideal V = (fittingIdeal G k).ideal V
    rw [Stacks.IdealSheaf.ideal_comap_appLE (fittingIdeal F k) f U V hVU]
    have : Module.Finite Γ(Y, U.1) Γ(F, U.1) := moduleFinite_sections_on_affine F U.1 U.2
    have : Module.Finite Γ(X, V.1) Γ(G, V.1) := moduleFinite_sections_on_affine G V.1 V.2
    rw [fittingIdeal_ideal F k U, fittingIdeal_ideal G k V]
    exact moduleFittingIdeal_map_eq_of_extendScalars_iso (f.appLE U.1 V.1 hVU)
      (affinePullbackSectionsBaseChangeIso f F U.2 V.2 hVU) k

/-- A quasi-coherent ideal sheaf is of finite type when its ideal on every affine
open is finitely generated. -/
def Scheme.IdealSheafData.IsFiniteType {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ U, (I.ideal U).FG

/-- The `r`-th Fitting ideal sheaf, indexed by a natural number: the specialization of the
integer-indexed `AlgebraicGeometry.fittingIdeal`, so that the base-change and finite-type
results are about the same ideal sheaf. -/
noncomputable def fittingIdealOfNat {X : Scheme.{u}} (F : X.Modules) (r : ℕ) :
    X.IdealSheafData :=
  fittingIdeal F (r : ℤ)

/-- The sections of a finitely presented module on an affine open are a finitely presented
module over the ring of functions there. -/
theorem finitePresentation_sections_on_affine {X : Scheme.{u}}
    (F : X.Modules) [F.IsFinitePresentation] (U : X.affineOpens) :
    Module.FinitePresentation Γ(X, U.1) Γ(F, U.1) := by
  let f := U.2.fromSpec
  have : IsOpenImmersion f := U.2.isOpenImmersion_fromSpec
  let G := F.restrict f
  have : G.IsFinitePresentation := AlgebraicGeometry.finitePresentation_restrict f F
  have : G.IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation G
  have : Module.FinitePresentation Γ(X, U.1) Γ(G, ⊤) := finitePresentation_sections_of_affine G
  exact Module.FinitePresentation.of_equiv (affineSectionsLinearEquiv F U.2)

/-- The Fitting ideals of a finitely presented sheaf of modules are
quasi-coherent ideals of finite type. -/
@[stacks 0C3E]
lemma fittingIdeal_isFiniteType {X : Scheme.{u}} (F : X.Modules)
    [F.IsFinitePresentation] (r : ℕ) :
    Scheme.IdealSheafData.IsFiniteType (fittingIdealOfNat F r) := by
  intro U
  have : Module.FinitePresentation Γ(X, U.1) Γ(F, U.1) :=
    finitePresentation_sections_on_affine F U
  have : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  change ((fittingIdeal F (r : ℤ)).ideal U).FG
  rw [fittingIdeal_ideal]
  exact (fittingIdeal_basic_properties.{u, u, u, u} (R := Γ(X, U.1))
    (M := Γ(F, U.1))).2.2.2.1 inferInstance r

end AlgebraicGeometry
