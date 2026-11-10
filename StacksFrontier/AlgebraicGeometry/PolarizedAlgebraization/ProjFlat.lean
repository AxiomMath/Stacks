module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleDegreeZeroFlat
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeProj.FlatOverBase
public import StacksFrontier.AlgebraicGeometry.RelativeProjFinitePresentation.GradedBaseChange
public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayFlatOverBase

/-!
# The projective spectrum of a graded algebra over a base ring

Let `R` be a commutative ring and `B` a graded `R`-algebra with grading `𝒢 : ℕ → Submodule R B`.
The structure morphism `Proj 𝒢 ⟶ Spec R` is `Proj 𝒢 ⟶ Spec (𝒢 0) ⟶ Spec R`. This file records
its basic properties in terms of the graded pieces and of `B` as an `R`-algebra.

## Main results

* `AlgebraicGeometry.Proj.flat_toSpecZero_comp_algebraMap`: `Proj 𝒢` is flat over `Spec R` when
  every graded piece is a flat `R`-module.
* `AlgebraicGeometry.Proj.isFlatOver_twistingSheaf`: every twist `𝒪(t)` of `Proj 𝒢` is then flat
  over `Spec R` (the absolute form of Stacks tag 0D4C).
* `AlgebraicGeometry.Proj.finitePresentation_toSpecZero_comp_algebraMap`: `Proj 𝒢` is of finite
  presentation over `Spec R` when `B` is a finitely presented `R`-algebra.
* `AlgebraicGeometry.Proj.isProper_toSpecZero_comp_algebraMap`: `Proj 𝒢` is proper over `Spec R`
  when `B` is a finitely generated `R`-algebra and `𝒢 0` is a finite `R`-module.

## Implementation notes

Flatness of a twist is checked on the affine cover of `Proj 𝒢` by the standard opens `D₊(f)` at
homogeneous elements of positive degree, over the single affine open `Spec R` of the base
(`AlgebraicGeometry.isFlatOver_tfae`). On `D₊(f)` the sections of `𝒪(t)` are the degree-zero part
of the localization of the shifted ring `B(t)` away from `f`, a direct limit of graded pieces of
`B` (`AlgebraicGeometry.ProjectiveSpectrum.Proj.flat_degreeZeroLocalization`). That criterion
reads the pieces with the `R`-module structure obtained through `R → 𝒢 0 → B`, which agrees with
the given one only propositionally; `compHomSubmodule` presents a piece for that structure.

## References

* [Stacks Project, Tag 0D4C](https://stacks.math.columbia.edu/tag/0D4C)
* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

/-- The grading action of natural-number ring degrees on integer module degrees, by addition, as
in the files defining the integer-graded twist of a graded ring. -/
local instance projFlatDegreeVAdd : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

/-- Flatness transported along a bijective ring homomorphism of the scalars. -/
private theorem flat_compHom_of_bijective {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] [Module.Flat S M] (e : R →+* S) (he : Function.Bijective e) :
    letI := Module.compHom M e
    Module.Flat R M := by
  let := Module.compHom M e
  let := e.toAlgebra
  have : IsScalarTower R S M := ⟨fun r s m => by
    change (e r * s) • m = e r • s • m
    rw [mul_smul]⟩
  have : Module.Flat R S := RingHom.Flat.of_bijective he
  exact Module.Flat.trans R S M

/-- An `R`-submodule of an `R`-algebra, read for the `R`-module structure obtained by restricting
scalars along a ring homomorphism agreeing with the structure map. -/
private def compHomSubmodule {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (ψ : R →+* B) (hψ : ∀ r, ψ r = algebraMap R B r) (N : Submodule R B) :
    letI := Module.compHom B ψ
    Submodule R B :=
  letI := Module.compHom B ψ
  { carrier := N
    add_mem' := add_mem
    zero_mem' := zero_mem _
    smul_mem' := fun r x hx => by
      change ψ r * x ∈ N
      rw [hψ, ← Algebra.smul_def]
      exact N.smul_mem r hx }

/-- Flatness of a submodule does not see the change of `R`-module structure of
`compHomSubmodule`. -/
private theorem flat_compHomSubmodule {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (ψ : R →+* B) (hψ : ∀ r, ψ r = algebraMap R B r) (N : Submodule R B) [Module.Flat R N] :
    letI := Module.compHom B ψ
    Module.Flat R (compHomSubmodule ψ hψ N) := by
  let := Module.compHom B ψ
  let e : compHomSubmodule ψ hψ N ≃ₗ[R] N :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => Subtype.ext (by
        change ψ r * x.1 = _
        rw [hψ, ← Algebra.smul_def]
        rfl) }
  exact Module.Flat.of_linearEquiv e

namespace AlgebraicGeometry.Proj

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (𝒢 : ℕ → Submodule R B) [GradedAlgebra 𝒢]

private theorem toSubmodules_eq (i : ℕ) :
    GradedRing.toSubmodules 𝒢 (SetLike.algebraMap_mem_graded 𝒢) i = 𝒢 i :=
  Submodule.ext fun _ => Iff.rfl

private theorem toGradeZero_eq :
    GradedRing.toGradeZero 𝒢 (SetLike.algebraMap_mem_graded 𝒢) = algebraMap R (𝒢 0) :=
  RingHom.ext fun _ => Subtype.ext rfl

/-- **`Proj 𝒢` is flat over `Spec R`** when every graded piece of `𝒢` is a flat `R`-module. -/
theorem flat_toSpecZero_comp_algebraMap (hflat : ∀ d, Module.Flat R (𝒢 d)) :
    Flat (Proj.toSpecZero 𝒢 ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(𝒢 0)))) := by
  refine flat_toSpecZero_comp_of_flat_away_forall 𝒢 _ fun m f => ?_
  have h := Away.flat_fromZeroRingHom_comp 𝒢 (SetLike.algebraMap_mem_graded 𝒢) (a := (f : B)) f.2 0
    (fun n _ => by rw [toSubmodules_eq]; exact hflat _)
  rwa [toGradeZero_eq] at h

/-- **`Proj 𝒢` is of finite presentation over `Spec R`** when `B` is a finitely presented
`R`-algebra. -/
theorem finitePresentation_toSpecZero_comp_algebraMap [Algebra.FinitePresentation R B] :
    _root_.AlgebraicGeometry.FinitePresentation
      (Proj.toSpecZero 𝒢 ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(𝒢 0)))) := by
  have : Algebra.FiniteType (𝒢 0) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (𝒢 0) B
  have := Stacks.AlgebraicGeometry.Proj.locallyOfFinitePresentation_projToSpec 𝒢
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **`Proj 𝒢` is proper over `Spec R`** when `B` is a finitely generated `R`-algebra whose
degree-zero part is a finite `R`-module.

The second hypothesis cannot be dropped: for `B = R[x, y]` with `x` of degree `0` and `y` of
degree `1`, `Proj 𝒢` is the affine line over `R`. -/
theorem isProper_toSpecZero_comp_algebraMap [Algebra.FiniteType R B] [Module.Finite R (𝒢 0)] :
    IsProper (Proj.toSpecZero 𝒢 ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(𝒢 0)))) := by
  have : Algebra.FiniteType (𝒢 0) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (𝒢 0) B
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R ↥(𝒢 0)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  infer_instance

/-- **The structure morphism of `Proj 𝒢` over `Spec R`, on the sections over a standard open.**
It is `Γ(Spec R, ⊤) ≅ R ⟶ 𝒢 0 ⟶ 𝒢_(f)` followed by the identification of `𝒢_(f)` with the
functions on `D₊(f)`. -/
theorem appLE_toSpecZero_comp_algebraMap {f : B} {d : ℕ} (hf : f ∈ 𝒢 d) (hd : 0 < d)
    (h : Proj.basicOpen 𝒢 f ≤
      (Proj.toSpecZero 𝒢 ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(𝒢 0)))) ⁻¹ᵁ ⊤) :
    (Proj.toSpecZero 𝒢 ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(𝒢 0)))).appLE ⊤
        (Proj.basicOpen 𝒢 f) h =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
        CommRingCat.ofHom ((fromZeroRingHom 𝒢 (Submonoid.powers f)).comp
          (algebraMap R ↥(𝒢 0))) ≫ Proj.awayToSection 𝒢 f := by
  have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of R)).Opens) := isAffineOpen_top _
  have hV := Proj.isAffineOpen_basicOpen 𝒢 f hf hd
  have ht : (Proj.basicOpen 𝒢 f).ι ≫ Proj.toSpecZero 𝒢 =
      Proj.basicOpenToSpec 𝒢 f ≫
        Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒢 (Submonoid.powers f))) := by
    rw [← Proj.awayι_toSpecZero 𝒢 f hf hd]
    simp [Proj.awayι, ← Proj.basicOpenIsoSpec_hom 𝒢 f hf hd]
  apply Spec.map_injective
  apply (cancel_mono hU.fromSpec).mp
  apply (cancel_epi hV.isoSpec.hom).mp
  rw [← Category.assoc, hV.isoSpec_hom, Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc,
    ← hU.isoSpec_hom, hU.isoSpec_hom_fromSpec, Scheme.Hom.resLE_comp_ι]
  have hiso : Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ hU.fromSpec = 𝟙 _ := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id]
  have hb : (Proj.basicOpen 𝒢 f).toSpecΓ ≫ Spec.map (Proj.awayToSection 𝒢 f) =
      Proj.basicOpenToSpec 𝒢 f := rfl
  rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hiso, Category.comp_id,
    ← Category.assoc, ← Category.assoc, hb, CommRingCat.ofHom_comp, Spec.map_comp,
    ← Category.assoc, ← ht, Category.assoc]

/-- **The sections of a twist of `Proj 𝒢` over a standard open are flat over `R`** when every
graded piece of `𝒢` is a flat `R`-module: they are the degree-zero part of the twisted
localization, a direct limit of graded pieces. -/
theorem flat_twistSections (hflat : ∀ d, Module.Flat R (𝒢 d)) {f : B} {d : ℕ} (hf : f ∈ 𝒢 d)
    (hd : 0 < d) (t : ℤ) :
    let T : (Proj 𝒢).Modules := twistingSheaf 𝒢 t
    letI : Module R Γ(T, Proj.basicOpen 𝒢 f) :=
      Module.compHom _ ((Proj.awayToSection 𝒢 f).hom.comp
        ((fromZeroRingHom 𝒢 (Submonoid.powers f)).comp (algebraMap R ↥(𝒢 0))))
    Module.Flat R Γ(T, Proj.basicOpen 𝒢 f) := by
  let T : (Proj 𝒢).Modules := twistingSheaf 𝒢 t
  let φ : R →+* Away 𝒢 f := (fromZeroRingHom 𝒢 (Submonoid.powers f)).comp (algebraMap R ↥(𝒢 0))
  let _ : Module R Γ(T, Proj.basicOpen 𝒢 f) :=
    Module.compHom _ ((Proj.awayToSection 𝒢 f).hom.comp φ)
  let _ : Module R (GradedModuleDegreeZeroLocalization 𝒢 (twistGrading 𝒢 t) f) :=
    Module.compHom _ φ
  let e := associatedModuleSheafStandardOpenEquiv 𝒢 (twistGrading 𝒢 t) hf hd
  let eR : Γ(T, Proj.basicOpen 𝒢 f) ≃ₗ[R]
      GradedModuleDegreeZeroLocalization 𝒢 (twistGrading 𝒢 t) f :=
    { e.toAddEquiv with map_smul' := fun r x => e.map_smul (φ r) x }
  refine (Module.Flat.equiv_iff eR).mpr ?_
  let K : ℕ := t.natAbs
  have hbound (i : ℕ) : 0 ≤ (((K + i) * d : ℕ) : ℤ) + t := by
    have := Nat.le_mul_of_pos_right (K + i) hd
    omega
  let j : ℕ → ℕ := fun i => ((((K + i) * d : ℕ) : ℤ) + t).toNat
  have hψ : ∀ r, ((algebraMap (𝒢 0) B).comp (algebraMap R (𝒢 0))) r = algebraMap R B r :=
    fun _ => rfl
  refine flat_degreeZeroLocalization 𝒢 (twistGrading 𝒢 t) (algebraMap R (𝒢 0)) hf K
    (fun i => compHomSubmodule _ hψ (𝒢 (j i))) ?_ ?_
  · intro i x
    have hdeg : (K + i) • (d : ℤ) + t = ((j i : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (hbound i)]
      push_cast
      ring
    rw [twistGrading_apply, hdeg, integerGrading_natCast]
    exact Iff.rfl
  · intro i
    have := hflat (j i)
    exact flat_compHomSubmodule _ hψ (𝒢 (j i))


/-- **Every twist of `Proj 𝒢` is flat over `Spec R`** when every graded piece of `𝒢` is a flat
`R`-module. This is the absolute form of the second assertion of Stacks tag 0D4C. -/
theorem isFlatOver_twistingSheaf (hflat : ∀ d, Module.Flat R (𝒢 d)) (t : ℤ) :
    IsFlatOver
      (Proj.toSpecZero 𝒢 ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(𝒢 0)))).toLRSHom.toShHom
      (twistingSheaf 𝒢 t) := by
  classical
  let p := Proj.toSpecZero 𝒢 ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(𝒢 0)))
  let F : (Proj 𝒢).Modules := twistingSheaf 𝒢 t
  have : F.IsQuasicoherent :=
    (inferInstance : SheafOfModules.IsQuasicoherent.{u, u, u} (twistingSheaf 𝒢 t))
  refine ((isFlatOver_tfae p F).out 4 1).mp ?_
  refine ⟨PUnit, fun _ => ⊤, TopologicalSpace.IsOpenCover.mk (iSup_const), fun _ =>
    isAffineOpen_top _, fun _ => ?_⟩
  let V : (Σ m : ℕ+, 𝒢 (m : ℕ)) → (Proj 𝒢).Opens := fun i => Proj.basicOpen 𝒢 (i.2 : B)
  refine ⟨_, V, ?_, fun i => Proj.isAffineOpen_basicOpen 𝒢 _ i.2.2 i.1.2, fun i => ?_⟩
  · rw [iSup_basicOpen_homogeneous_eq_top]
    rfl
  · intro hUV
    rw [appLE_toSpecZero_comp_algebraMap 𝒢 i.2.2 i.1.2]
    let _ : Module R Γ(F, V i) :=
      Module.compHom _ ((Proj.awayToSection 𝒢 (i.2 : B)).hom.comp
        ((fromZeroRingHom 𝒢 (Submonoid.powers (i.2 : B))).comp (algebraMap R ↥(𝒢 0))))
    have : Module.Flat R Γ(F, V i) := flat_twistSections 𝒢 hflat i.2.2 i.1.2 t
    exact flat_compHom_of_bijective (M := Γ(F, V i)) (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom)


end AlgebraicGeometry.Proj

end
