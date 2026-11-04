module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.CechVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.CechComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Twist
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Flat base change for the cohomology of projective space, and regularity over a field extension

For a faithfully flat ring map `A ⟶ B` and a quasi-coherent module `ℱ` on `ℙⁿ_A`, the cohomology
`Hᵖ(ℙⁿ_A, ℱ)` vanishes if and only if `Hᵖ(ℙⁿ_B, g^*ℱ)` does, in **every** degree `p`. This is the
vanishing consequence of [Stacks, Tag 02KH] part (2) for projective space, and it is what
[Stacks, Tag 08A4] is: a coherent sheaf on `ℙⁿ_k` is `m`-regular exactly when its pullback to
`ℙⁿ_K` is, for `k ⊆ K` an extension of fields.

Both cohomologies are computed by the Čech complex of the `n + 1`
standard charts (`Stacks.Cohomology.CechVanishing.isZero_Hgroup_iff_isZero_cechHomology`, the
charts having affine intersections); the Čech complex upstairs is the base change along
`A ⟶ B` of the Čech complex downstairs
(`Stacks.ProjectiveCohomology.cechBaseChangeIsoChart`, which uses no flatness); extension of
scalars along a flat ring map commutes with homology; and a faithfully flat extension of scalars
reflects vanishing.

## Main results

* `Stacks.ProjectiveCohomology.isZero_homology_restrict_extend_iff`: the ring-level core — for a
  faithfully flat `ψ`, the `p`-th homology of the base change of a cochain complex of modules
  vanishes exactly when the `p`-th homology of the complex does.
* `Stacks.ProjectiveCohomology.respectsIso_appLE_spec_map`: every iso-respecting property of ring
  maps transfers from `φ` to the map `Spec φ` induces on global sections, and
  `faithfullyFlat_appLE_spec_map` is its faithfully-flat case.
* `Stacks.ProjectiveCohomology.isZero_cechHomology_chart_baseChange_iff`: base change for the
  homology of the Čech complex of the standard charts.
* `AlgebraicGeometry.isZero_Hgroup_projectiveSpace_baseChange_iff`: **[Stacks, Tag 02KH] part (2)
  for projective space, as a vanishing criterion, in every degree.**
* `AlgebraicGeometry.isCoherent_projectiveTwist`: a twist of a coherent module on projective
  space is coherent.
* `AlgebraicGeometry.isMRegular_iff_fieldExtension`: **[Stacks, Tag 08A4]**.

## Implementation notes

The base change in `Stacks.ProjectiveCohomology.cechBaseChangeIsoChart` is along
`Γ(Spec A, ⊤) ⟶ Γ(Spec B, ⊤)`, not along `Γ(ℙⁿ_A, ⊤) ⟶ Γ(ℙⁿ_B, ⊤)`, so the flatness needed is
that of `φ` itself, transported along `AlgebraicGeometry.Scheme.ΓSpecIso`. Flatness makes
extension of scalars commute with homology, and faithfulness reflects vanishing.

More general forms of `isZero_restrictScalars_iff` (over `Ring`) and of `isZero_extendScalars_iff`
(for `algebraMap A B`) are in `StacksFrontier.Homology.TorAmplitude.FaithfullyFlat`; the map this
file feeds the latter is `(q.appLE ⊤ ⊤).hom`, which is not an `algebraMap`.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 08A3](https://stacks.math.columbia.edu/tag/08A3)
* [Stacks Project, Tag 08A4](https://stacks.math.columbia.edu/tag/08A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.CechSheaf (SectionRing cechComplex)
open Stacks.Cohomology.CechAcyclic (preservesHomology_restrictScalars)
open Stacks.AlgebraicGeometry.SectionsBaseChange (le_preimage_top)

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Stacks.ProjectiveCohomology

/-! ### Vanishing under change of rings -/

/-- Restriction of scalars reflects and preserves vanishing. -/
public theorem isZero_restrictScalars_iff {R S : Type u} [CommRing R] [CommRing S] (ψ : R →+* S)
    (M : ModuleCat.{u} S) :
    IsZero ((ModuleCat.restrictScalars.{u} ψ).obj M) ↔ IsZero M := by
  simp only [ModuleCat.isZero_iff_subsingleton]
  rfl

/-- **A faithfully flat extension of scalars reflects vanishing.** -/
public theorem isZero_extendScalars_iff {R S : Type u} [CommRing R] [CommRing S] (ψ : R →+* S)
    (hff : ψ.FaithfullyFlat) (M : ModuleCat.{u} R) :
    IsZero ((ModuleCat.extendScalars.{u, u, u} ψ).obj M) ↔ IsZero M := by
  let _ := ψ.toAlgebra
  have : Module.FaithfullyFlat R S := hff
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R S

/-- Restriction of scalars preserves and reflects vanishing of the homology of a complex. -/
public theorem isZero_homology_restrictScalars_iff {R S : Type u} [CommRing R] [CommRing S]
    (ψ : R →+* S) (K : CochainComplex (ModuleCat.{u} S) ℕ) (p : ℕ) :
    IsZero ((((ModuleCat.restrictScalars.{u} ψ).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology p) ↔ IsZero (K.homology p) :=
  have := preservesHomology_restrictScalars ψ
  ((K.sc p).mapHomologyIso (ModuleCat.restrictScalars.{u} ψ)).isZero_iff.trans
    (isZero_restrictScalars_iff ψ (K.homology p))

/-- **Base change of a complex of modules along a faithfully flat ring map reflects vanishing of
homology.** -/
public theorem isZero_homology_extendScalars_iff {R S : Type u} [CommRing R] [CommRing S]
    (ψ : R →+* S) (hff : ψ.FaithfullyFlat) (K : CochainComplex (ModuleCat.{u} R) ℕ) (p : ℕ) :
    IsZero ((((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology p) ↔ IsZero (K.homology p) :=
  have := extendScalars_preservesHomology_of_flat.{u, u} ψ hff.flat
  ((K.sc p).mapHomologyIso (ModuleCat.extendScalars.{u, u, u} ψ)).isZero_iff.trans
    (isZero_extendScalars_iff ψ hff (K.homology p))

/-- Restricting the coefficients of a complex of modules along `ρ` and then extending them along
a faithfully flat `ψ` preserves and reflects vanishing of homology. -/
public theorem isZero_homology_restrict_extend_iff {R₀ R₁ R₂ : Type u} [CommRing R₀]
    [CommRing R₁] [CommRing R₂] (ρ : R₀ →+* R₁) (ψ : R₀ →+* R₂) (hff : ψ.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{u} R₁) ℕ) (p : ℕ) :
    IsZero ((((ModuleCat.restrictScalars.{u} ρ ⋙ ModuleCat.extendScalars.{u, u, u} ψ
        ).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology p) ↔
      IsZero (K.homology p) :=
  (HomologicalComplex.homologyMapIso
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.restrictScalars.{u} ρ ⋙ ModuleCat.extendScalars.{u, u, u} ψ))
        (ComplexShape.up ℕ)).app K).symm p).isZero_iff.trans
    ((isZero_homology_extendScalars_iff ψ hff _ p).trans
      (isZero_homology_restrictScalars_iff ρ K p))

/-! ### The ring map on global sections of an affine scheme -/

/-- **Every iso-respecting property of ring maps transfers from `φ` to the map `Spec φ` induces
on global sections.**

`Stacks.AlgebraicGeometry.SectionsBaseChange.flat_appLE_Spec_map` is the case
`P = RingHom.Flat`. -/
public theorem respectsIso_appLE_spec_map
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hP : RingHom.RespectsIso @P) {A B : CommRingCat.{u}} (φ : A ⟶ B) (h : P φ.hom) :
    P ((Spec.map φ).appLE ⊤ ⊤ (le_preimage_top (Spec.map φ) ⊤)).hom := by
  have key : P (((Scheme.ΓSpecIso A).hom ≫ φ) ≫ (Scheme.ΓSpecIso B).inv :
      Γ(Spec A, ⊤) ⟶ Γ(Spec B, ⊤)).hom := by
    rw [CommRingCat.hom_comp,
      hP.cancel_right_isIso ((Scheme.ΓSpecIso A).hom ≫ φ) (Scheme.ΓSpecIso B).inv,
      CommRingCat.hom_comp, hP.cancel_left_isIso (Scheme.ΓSpecIso A).hom φ]
    exact h
  rw [(Spec.map φ).appLE_congr (le_preimage_top (Spec.map φ) ⊤) rfl
      ((Spec.map φ).preimage_top).symm (fun g => P g.hom), Scheme.Hom.appLE_eq_app,
    show (Spec.map φ).app (⊤ : (Spec A).Opens)
      = ((Scheme.ΓSpecIso A).hom ≫ φ) ≫ (Scheme.ΓSpecIso B).inv from
      (Iso.eq_comp_inv _).2 (Scheme.ΓSpecIso_naturality φ)]
  exact key

/-- **`Spec` of a faithfully flat ring map is faithfully flat on global sections.** -/
public theorem faithfullyFlat_appLE_spec_map {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (h : φ.hom.FaithfullyFlat) :
    ((Spec.map φ).appLE ⊤ ⊤ (le_preimage_top (Spec.map φ) ⊤)).hom.FaithfullyFlat :=
  respectsIso_appLE_spec_map RingHom.FaithfullyFlat.respectsIso φ h

/-! ### Base change for the Čech complex of the standard charts -/

/-- **Base change for the homology of the Čech complex of the standard charts of projective
space.** For a faithfully flat `A ⟶ B` and a quasi-coherent `ℱ` on `ℙⁿ_A`, the `p`-th homology of
the Čech complex of the standard charts of `ℙⁿ_B` with coefficients in `g^*ℱ` vanishes exactly
when that of `ℱ` on `ℙⁿ_A` does. -/
public theorem isZero_cechHomology_chart_baseChange_iff (n : ℕ) {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (hff : φ.hom.FaithfullyFlat)
    (F : (projectiveSpaceOverRing n A).Modules) [F.IsQuasicoherent] (p : ℕ) :
    IsZero ((cechComplex.{u, u, u, u} (R := (projectiveSpaceOverRing n A).ringCatSheaf) ⊤
        (chartAtUniverse n A) (iSup_chartAtUniverse_eq_top n A).symm F).homology p) ↔
      IsZero ((cechComplex.{u, u, u, u} (R := (projectiveSpaceOverRing n B).ringCatSheaf) ⊤
        (chartAtUniverse n B) (iSup_chartAtUniverse_eq_top n B).symm
        ((Scheme.Modules.pullback (projectiveSpaceOverRingMap n φ)).obj F)).homology p) := by
  have h1 := isZero_homology_restrict_extend_iff
    ((pullback.fst (terminal.from (Spec A))
      (terminal.from (projectiveSpaceAtUniverse.{u} n))).appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom
    ((Spec.map φ).appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom
    (faithfullyFlat_appLE_spec_map φ hff)
    (cechComplex.{u, u, u, u} (R := (projectiveSpaceOverRing n A).ringCatSheaf) ⊤
      (chartAtUniverse n A) (iSup_chartAtUniverse_eq_top n A).symm F) p
  have h2 := isZero_homology_restrictScalars_iff
    ((pullback.fst (terminal.from (Spec B))
      (terminal.from (projectiveSpaceAtUniverse.{u} n))).appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom
    (cechComplex.{u, u, u, u} (R := (projectiveSpaceOverRing n B).ringCatSheaf) ⊤
      (chartAtUniverse n B) (iSup_chartAtUniverse_eq_top n B).symm
      ((Scheme.Modules.pullback (projectiveSpaceOverRingMap n φ)).obj F)) p
  exact h1.symm.trans
    ((HomologicalComplex.homologyMapIso (cechBaseChangeIsoChart n φ F) p).isZero_iff.trans h2)

end Stacks.ProjectiveCohomology

namespace AlgebraicGeometry

open Stacks.ProjectiveCohomology

/-- **[Stacks, Tag 02KH] part (2) for projective space, as a vanishing criterion, in every
degree.** For a faithfully flat ring map `A ⟶ B` and a quasi-coherent module `ℱ` on `ℙⁿ_A`, the
cohomology `Hᵖ(ℙⁿ_A, ℱ)` vanishes if and only if `Hᵖ(ℙⁿ_B, g^*ℱ)` does. -/
public theorem isZero_Hgroup_projectiveSpace_baseChange_iff (n : ℕ) {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (hff : φ.hom.FaithfullyFlat)
    (F : (projectiveSpaceOverRing n A).Modules) [F.IsQuasicoherent] (p : ℕ) :
    IsZero (Hgroup (projectiveSpaceOverRing n A).ringCatSheaf ⊤ p F) ↔
      IsZero (Hgroup (projectiveSpaceOverRing n B).ringCatSheaf ⊤ p
        ((Scheme.Modules.pullback (projectiveSpaceOverRingMap n φ)).obj F)) :=
  (Stacks.Cohomology.CechVanishing.isZero_Hgroup_iff_isZero_cechHomology
      (projectiveSpaceOverRing n A) ⊤ (chartAtUniverse n A)
      (iSup_chartAtUniverse_eq_top n A).symm
      (fun _ s => isAffineOpen_iInf_chartAtUniverse n A s) F p).trans
    ((isZero_cechHomology_chart_baseChange_iff n φ hff F p).trans
      (Stacks.Cohomology.CechVanishing.isZero_Hgroup_iff_isZero_cechHomology
        (projectiveSpaceOverRing n B) ⊤ (chartAtUniverse n B)
        (iSup_chartAtUniverse_eq_top n B).symm
        (fun _ s => isAffineOpen_iInf_chartAtUniverse n B s) _ p).symm)

/-! ### Coherence of a twist -/

/-- The pullback to `ℙⁿ_R` of the integral twisting sheaf is invertible. -/
public theorem isInvertible_pullback_projectiveSpaceAtUniverseTwistingSheaf
    {R : Type u} [CommRing R] (n : ℕ) (d : ℤ) :
    SheafOfModules.IsInvertible
      (projectiveSpaceOverRing n (.of R)).presheaf
      (projectiveSpaceOverRing n (.of R)).ringCatSheaf.2
      ((Scheme.Modules.pullback
        (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R)))).obj
        (projectiveSpaceAtUniverseTwistingSheaf n d)) := by
  have h0 : SheafOfModules.IsInvertible
      (projectiveSpaceAtUniverse.{u} n).presheaf
      (projectiveSpaceAtUniverse.{u} n).ringCatSheaf.2
      (projectiveSpaceAtUniverseTwistingSheaf n d) := by
    dsimp [projectiveSpaceAtUniverseTwistingSheaf, projectiveSpaceAtUniverse]
    exact ProjectiveSpectrum.Proj.projectiveSpace_isInvertible_twistingSheaf
      (ULift.{u} ℤ) (n + 1) d
  have h1 : Stacks.SheafOfModules.IsInvertible
      (projectiveSpaceAtUniverse.{u} n).presheaf
      (structureSheafRing
        (projectiveSpaceAtUniverse.{u} n).toRingedSpace).property
      (projectiveSpaceAtUniverseTwistingSheaf n d) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2 h0
  exact (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
    (Stacks.Modules.isInvertible_pullback
      (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R)))
      (projectiveSpaceAtUniverseTwistingSheaf n d))

/-- **A twist of a coherent module on projective space is coherent.** -/
public theorem isCoherent_projectiveTwist {R : Type u} [CommRing R] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of R)).Modules) [F.IsCoherent] (d : ℤ) :
    (projectiveTwist n F d).IsCoherent :=
  have := isInvertible_pullback_projectiveSpaceAtUniverseTwistingSheaf (R := R) n d
  SheafOfModules.isCoherent_tensorSheaf_of_isInvertible
    (projectiveSpaceOverRing n (.of R)) F _

/-- A twist of a coherent module on projective space is quasi-coherent.

`AlgebraicGeometry.isQuasicoherent_projectiveTwist` is the same conclusion under the weaker
hypothesis that the module is quasi-coherent. -/
public theorem isQuasicoherent_projectiveTwist_of_isCoherent {R : Type u} [CommRing R] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of R)).Modules) [F.IsCoherent] (d : ℤ) :
    (projectiveTwist n F d).IsQuasicoherent :=
  have := isCoherent_projectiveTwist n F d
  isQuasicoherent_of_isCoherent _

/-! ### Tag 08A4 -/

/-- **[Stacks, Tag 08A4].** Let `k ⊆ K` be an extension of fields and let `ℱ` be a coherent sheaf
on `ℙⁿ_k`. Then `ℱ` is `m`-regular if and only if its pullback to `ℙⁿ_K` is `m`-regular. -/
@[stacks 08A4]
public theorem isMRegular_iff_fieldExtension (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : ℕ) (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] (m : ℤ) :
    letI : IsLocallyNoetherian (projectiveSpaceOverRing n (.of K)) :=
      projectiveSpaceOver_isLocallyNoetherian n (Spec (.of K))
    letI : ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k K n)).obj F).IsCoherent :=
      isCoherent_pullback (projectiveSpaceFieldExtensionMap k K n) F
    IsMRegular k n F m ↔
      IsMRegular K n
        ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj F) m := by
  have hff : (CommRingCat.ofHom (algebraMap k K)).hom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  refine Iff.trans ?_ (isMRegular_pullback_iff_forall_isZero k K n F m).symm
  refine forall_congr' fun i => forall_congr' fun _ => forall_congr' fun _ => ?_
  have := isQuasicoherent_projectiveTwist_of_isCoherent n F (m - i)
  exact isZero_Hgroup_projectiveSpace_baseChange_iff n
    (CommRingCat.ofHom (algebraMap k K)) hff (projectiveTwist n F (m - i)) i

end AlgebraicGeometry

end
