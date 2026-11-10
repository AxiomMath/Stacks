module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.LocalProperties.Projective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.BaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.StandardRefinement
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Projective
public import StacksFrontier.RingTheory.Flat.Localization
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingModuleProperties

/-!
# Locally projective modules and affine covers

A quasi-coherent sheaf of modules on a scheme is locally projective as soon as its sections are
projective on the members of *some* affine open cover: projectivity of sections propagates from
an affine open to its principal opens because sections over a principal open are a localization
of the sections over the ambient affine, and projectivity over a ring follows from projectivity
of the localizations at a finite family generating the unit ideal, by formal glueing.

Consequently local projectivity is detected on `Spec R` by projectivity of the module whose
associated sheaf is being considered.

## Main results

* `AlgebraicGeometry.isLocallyProjective_iff_exists_affineOpen_cover`: local projectivity of a
  quasi-coherent module is equivalent to projectivity of its sections on the members of one
  affine open cover.
* `AlgebraicGeometry.isLocallyProjective_tilde_iff_projective`: on the spectrum of a ring, the
  associated sheaf of a module is locally projective exactly when the module is projective.

## Implementation notes

Local projectivity is `AlgebraicGeometry.Scheme.Modules.IsLocallyProjective` of Tag 05JP. An
open covering is a `TopologicalSpace.IsOpenCover`. The localization statement for sections over
a principal open is `AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs` of
Tag 01P7, and the formal-glueing input is
`FormalGlueing.formalGlueing_preserves_moduleProperties_tensor_and_algebras`.

## References

* [Stacks Project, Tag 05JQ](https://stacks.math.columbia.edu/tag/05JQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry

private lemma projective_of_projective_localizations {R : Type u} [CommRing R]
    [Small.{u} R] {n : ℕ} (f : Fin n → R)
    (hf : Ideal.span (Set.range f) = (⊤ : Ideal R)) (M : Type u)
    [AddCommGroup M] [Module R M]
    (h : ∀ i, Module.Projective (Localization.Away (f i))
      (LocalizedModule.Away (f i) M)) : Module.Projective R M := by
  classical
  let S := PUnit
  let : CommRing S := inferInstance
  let φ : R →+* S :=
    { toFun := fun _ => PUnit.unit
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let : Algebra R S := φ.toAlgebra
  let c := FormalGlueing.moduleGlueingConstruction.{u, u, u} S f
  let := c.category
  have hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range f)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map) := by
    have : Subsingleton (R ⧸ Ideal.span (Set.range f)) := by
      rw [hf]
      infer_instance
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  obtain ⟨sourceTensor, genericTensor, localTensor, glueingTensor, e,
    hsym, hbg, hbl, hbc, hbs, hbf, hbi, hmono, he, hi, hprops, halg⟩ :=
    (FormalGlueing.formalGlueing_preserves_moduleProperties_tensor_and_algebras.{u, u, u}).1
      R S n f (by infer_instance) hq
  have hp := (hprops (ModuleCat.of R M)).2.2.2
  rw [he] at hp
  exact hp.mpr ⟨Module.Projective.of_equiv' (c.canonicalGeneric (ModuleCat.of R M)).symm,
    fun i => have := h i; Module.Projective.of_equiv' (c.canonicalLocal (ModuleCat.of R M) i).symm⟩

private lemma projective_sections_basicOpen {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (hM : Module.Projective Γ(X, U) Γ(M, U)) :
    Module.Projective Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) := by
  let : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  let : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom Γ(M, X.basicOpen f)
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let q := Scheme.Modules.restrictionLinearMap M
    (homOfLE (X.basicOpen_le f))
  let : IsLocalizedModule (Submonoid.powers f) q :=
    isLocalizedModule_restriction_basicOpen_of_qcqs M hU.isCompact
      hU.isQuasiSeparated f
  exact Module.projective_of_isLocalizedModule (Submonoid.powers f) q

/-- Projectivity transfers along a ring isomorphism and an additive bijection compatible
with the scalar actions. -/
private lemma projective_iff_of_ringEquiv {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (e : R ≃+* S) (g : M ≃+ N)
    (h : ∀ (r : R) (x : M), g (r • x) = e r • g x) :
    Module.Projective R M ↔ Module.Projective S N := by
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := ⟨by ext x; simp, by ext x; simp⟩
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := ⟨by ext x; simp, by ext x; simp⟩
  let q : M ≃ₛₗ[e.toRingHom] N := { g with map_smul' := h }
  exact ⟨fun _ => Module.Projective.of_equiv q, fun _ => Module.Projective.of_equiv q.symm⟩

private lemma projective_localizedModule_of_projective_sections {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) (hW :
      Module.Projective Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)) :
    Module.Projective (Localization.Away f) (LocalizedModule.Away f Γ(M, U)) := by
  classical
  let R := Γ(X, U)
  let N := Γ(M, U)
  let W := X.basicOpen f
  let B := Γ(X, W)
  let P := Γ(M, W)
  let : IsLocalization.Away f B := hU.isLocalization_basicOpen f
  let : Module R P := Module.compHom P (algebraMap R B)
  let e : Localization.Away f ≃ₐ[R] B :=
    IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) B
  let : Algebra (Localization.Away f) B := e.toAlgHom.toAlgebra
  let : Module (Localization.Away f) P := Module.compHom P (algebraMap _ B)
  let : IsScalarTower R (Localization.Away f) P :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      change e (algebraMap R (Localization.Away f) r) • m = algebraMap R B r • m
      rw [e.commutes r]
  let : Module R N := inferInstance
  let q : N →ₗ[R] P := Scheme.Modules.restrictionLinearMap M
    (homOfLE (X.basicOpen_le f))
  let : IsLocalizedModule.Away f q :=
    isLocalizedModule_restriction_basicOpen_of_qcqs M hU.isCompact
      hU.isQuasiSeparated f
  have hbase : IsBaseChange (Localization.Away f) q :=
    IsLocalizedModule.isBaseChange (Submonoid.powers f) (Localization.Away f) q
  let eM : LocalizedModule.Away f N ≃ₗ[Localization.Away f] P :=
    (LocalizedModule.equivTensorProduct (Submonoid.powers f) N).trans hbase.equiv
  have hP : Module.Projective (Localization.Away f) P := by
    refine (projective_iff_of_ringEquiv e.symm.toRingEquiv (AddEquiv.refl P) fun b x => ?_).1 hW
    change b • x = e (e.symm b) • x
    simp
  exact Module.Projective.of_equiv' eM.symm

/-- **Stacks Project, Tag 05JQ.** A quasi-coherent sheaf of modules is locally projective
if and only if its sections are projective on every member of some affine open cover. -/
@[stacks 05JQ "affine open cover characterization", sga "3 VIB 11.9.1" "(i) <=> (ii)"]
theorem isLocallyProjective_iff_exists_affineOpen_cover {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] :
    Scheme.Modules.IsLocallyProjective M ↔
      ∃ (ι : Type u) (U : ι → X.Opens),
        IsOpenCover U ∧
          (∀ i, IsAffineOpen (U i)) ∧
          ∀ i, Module.Projective Γ(X, U i) Γ(M, U i) := by
  classical
  refine ⟨fun h => ⟨X.affineOpens, fun U => U.1, IsOpenCover.mk (iSup_affineOpens_eq_top X),
    fun U => U.2, fun U => h U.1 U.2⟩, ?_⟩
  rintro ⟨ι, U, hcover, hUaff, hUproj⟩ V hV
  have htop : ⨆ i, U i = ⊤ := hcover
  obtain ⟨n, f, a, g, hstandard, hcoverV, heq⟩ :=
    Scheme.exists_isStandardOpenCover_basicOpen_eq_of_iSup_eq_top
      X U hUaff htop V hV
  have hspan : Ideal.span (Set.range f) = (⊤ : Ideal Γ(X, V)) := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    simpa [PrimeSpectrum.IsStandardOpenCoverOfSpectrum,
      PrimeSpectrum.IsStandardOpenCover, PrimeSpectrum.basicOpen_one] using hstandard
  have hloc (j : Fin n) :
      Module.Projective (Localization.Away (f j))
        (LocalizedModule.Away (f j) Γ(M, V)) := by
    apply projective_localizedModule_of_projective_sections M hV
    rw [heq j]
    exact projective_sections_basicOpen M (hUaff (a j)) (g j) (hUproj (a j))
  exact projective_of_projective_localizations f hspan Γ(M, V) hloc

/-- **Stacks Project, Tag 05JQ.** The sheaf associated to a module on an affine scheme is
locally projective if and only if the original module is projective. -/
@[stacks 05JQ "affine specialization", sga "3 VIB 11.9.1" "affine case"]
theorem isLocallyProjective_tilde_iff_projective (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) :
    Scheme.Modules.IsLocallyProjective (tilde M) ↔ Module.Projective R M := by
  have hq := projective_iff_of_ringEquiv (M := Γ(tilde M, ⊤))
    (N := (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (Opposite.op ⊤))
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv (AddEquiv.refl _) fun a x => by
      change a • x = (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv a • x
      rw [Scheme.Modules.smul_Spec_def]
      congr 1
      have hi : (⊤ : (Spec R).Opens).leTop = 𝟙 _ := Subsingleton.elim _ _
      simp [Iso.commRingCatIsoToRingEquiv, hi]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := hq.1 (h ⊤ (isAffineOpen_top _))
    exact Module.Projective.of_equiv' (tilde.isoTop M).symm.toLinearEquiv
  · have : Module.Projective R
        ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (Opposite.op ⊤)) :=
      Module.Projective.of_equiv' (tilde.isoTop M).toLinearEquiv
    exact (isLocallyProjective_iff_exists_affineOpen_cover (tilde M)).2
      ⟨PUnit, fun _ => ⊤, IsOpenCover.mk (by simp), fun _ => isAffineOpen_top _,
        fun _ => hq.2 this⟩

end AlgebraicGeometry
