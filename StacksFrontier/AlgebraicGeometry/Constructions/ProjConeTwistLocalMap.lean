module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeChart
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedPushforward
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStandardOpenScalars

/-!
# The degreewise inclusion `𝒪_P(m) ⟶ π_* 𝒪_L` over a standard open

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `π : L = Proj B ⟶ P` be the cone
attached to the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}`. For `f ∈ 𝒜 d` homogeneous of positive
degree the sections of `π_* 𝒪_L` over the standard open `D₊(f)` are the functions on
`π⁻¹(D₊(f)) = D₊(ψ f)`, that is the degree-zero localization `(B[1/ψ f])₀`, and
`Stacks.Truncation.awayGradingEquivSectionsTwist` identifies its degree-`m` summand with the
sections of the twisting sheaf `𝒪_P(m)` over `D₊(f)`.

This file turns that identification into a map of `Γ(P, D₊(f))`-modules

  `Γ(D₊(f), 𝒪_P(m)) ⟶ Γ(D₊(f), π_* 𝒪_L)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistAwayHom`: the degreewise inclusion
  `Γ(D₊(f), 𝒪_P(m)) →+ (B[1/ψ f])₀` as an additive map.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp`: the same map read into the sections of
  `π_* 𝒪_L` over `D₊(f)`, as a morphism of modules over the sections of `𝒪_P` there.

## Main results

* `Stacks.Truncation.awayToLocalization_map_psi`: the comparison map `(B[1/ψ f])₀ → A[1/f]`
  undoes `HomogeneousLocalization.Away.map ψ f`.
* `Stacks.Truncation.awayToLocalization_awayGradingEquivSectionsTwist_symm`: the degreewise
  inclusion, read in `A[1/f]`, is the standard-open description of a section of `𝒪_P(m)`.
* `Stacks.Truncation.awayGradingEquivSectionsTwist_symm_degree_indep`: the degreewise inclusion
  depends only on the standard open, not on the degree in which `f` is homogeneous.
* `Stacks.Truncation.awayGradingEquivSectionsTwist_symm_smul`: the degreewise inclusion is
  semilinear for `HomogeneousLocalization.Away.map ψ f`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.awayToSection_pi_app`: `π` on functions over `D₊(f)`,
  with the sections over `D₊(ψ f)` transported along `π⁻¹(D₊(f)) = D₊(ψ f)`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation

namespace Stacks.Truncation

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A}

/-- The comparison map `(B[1/ψ f])₀ → A[1/f]` undoes `HomogeneousLocalization.Away.map ψ f`:
the fraction `ψ a / (ψ f)ᵏ` of the truncation algebra is sent to the fraction `a / fᵏ`. -/
@[stacks 0EKG "the comparison map (B[1/psi f])_0 to A[1/f] undoes the map of degree-zero \
localizations attached to psi"]
theorem awayToLocalization_map_psi (d : ℕ) (hf : f ∈ 𝒜 d)
    (r : HomogeneousLocalization.Away 𝒜 f) :
    awayToLocalization 𝒜 (HomogeneousLocalization.Away.map (psi 𝒜) f r) = r.val := by
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf r
  have hx' : x ∈ 𝒜 (n * d) := by simpa only [smul_eq_mul] using hx
  have hxt : x ∈ truncation 𝒜 (n * d) := mem_truncation_of_mem 𝒜 le_rfl hx'
  rw [HomogeneousLocalization.Away.map_mk, HomogeneousLocalization.Away.val_mk,
    show HomogeneousLocalization.Away.mk (grading 𝒜) (GradedRingHom.map_mem (psi 𝒜) hf) n
        (psi 𝒜 x) (GradedRingHom.map_mem (psi 𝒜) hx) = awayElt 𝒜 d hf n x hxt from
      congrArg HomogeneousLocalization.mk
        (HomogeneousLocalization.NumDenSameDeg.ext _ (nsmul_eq_mul n d)
          (psi_eq_degElt 𝒜 x hx') rfl),
    awayToLocalization_awayElt 𝒜 d hf n x hxt]
  rfl

/-- The degreewise inclusion of `Γ(D₊(f), 𝒪_P(m))` into `(B[1/ψ f])₀`, read in `A[1/f]`, is the
standard-open description of the section it starts from. -/
theorem awayToLocalization_awayGradingEquivSectionsTwist_symm (d : ℕ) (hf : f ∈ 𝒜 d)
    (hd : 0 < d) (m : ℕ)
    (s : (twistingSheaf 𝒜 (m : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    awayToLocalization 𝒜
        (((awayGradingEquivSectionsTwist 𝒜 d hf hd m).symm s :
          HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f))) =
      ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd (m : ℤ) s :
        LocalizedModule.Away f A)) := by
  have h2 := congrArg (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading
    𝒜 hf hd (m : ℤ)) ((awayGradingEquivSectionsTwist 𝒜 d hf hd m).apply_symm_apply s)
  rw [show awayGradingEquivSectionsTwist 𝒜 d hf hd m
        ((awayGradingEquivSectionsTwist 𝒜 d hf hd m).symm s) =
      (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd (m : ℤ)).symm
        (awayPieceEquivAwayGrading 𝒜 d hf m (awayGradingEquivAwayPiece 𝒜 d hf m
          ((awayGradingEquivSectionsTwist 𝒜 d hf hd m).symm s))) from rfl,
    AddEquiv.apply_symm_apply] at h2
  exact congrArg Subtype.val h2

/-- The degreewise inclusion depends only on the standard open, not on the degree in which `f`
is homogeneous. -/
@[stacks 0EKG "the degreewise inclusion of the sections of O_P(m) over D+(f) into the functions \
on the cone depends only on the standard open, not on the degree of f"]
theorem awayGradingEquivSectionsTwist_symm_degree_indep {d d' : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hf' : f ∈ 𝒜 d') (hd' : 0 < d') (m : ℕ)
    (s : (twistingSheaf 𝒜 (m : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (((awayGradingEquivSectionsTwist 𝒜 d hf hd m).symm s :
        HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f))) =
      (((awayGradingEquivSectionsTwist 𝒜 d' hf' hd' m).symm s :
        HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f))) := by
  refine awayToLocalization_injective 𝒜 d hf ?_
  rw [awayToLocalization_awayGradingEquivSectionsTwist_symm,
    awayToLocalization_awayGradingEquivSectionsTwist_symm,
    Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading,
    Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading,
    associatedModuleSheafStandardOpenEquiv_degree_indep 𝒜 (twistGrading 𝒜 (m : ℤ))
      hf hd hf' hd' s]

/-- The degreewise inclusion `Γ(D₊(f), 𝒪_P(m)) → (B[1/ψ f])₀` is semilinear for the map
`HomogeneousLocalization.Away.map ψ f` of degree-zero localizations: scaling a section of
`𝒪_P(m)` by the degree-zero fraction `r` multiplies its image by the image of `r`. -/
@[stacks 0EKG "the degreewise inclusion is semilinear for the map of degree-zero localizations \
attached to psi, over one standard open D+(f)"]
theorem awayGradingEquivSectionsTwist_symm_smul (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) (m : ℕ)
    (r : HomogeneousLocalization.Away 𝒜 f)
    (s : (twistingSheaf 𝒜 (m : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (((awayGradingEquivSectionsTwist 𝒜 d hf hd m).symm
          ((ProjectiveSpectrum.Proj.awayToSection 𝒜 f).hom r • s) :
        HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f))) =
      HomogeneousLocalization.Away.map (psi 𝒜) f r *
        (((awayGradingEquivSectionsTwist 𝒜 d hf hd m).symm s :
          HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f))) := by
  refine awayToLocalization_injective 𝒜 d hf ?_
  rw [map_mul, awayToLocalization_awayGradingEquivSectionsTwist_symm,
    awayToLocalization_awayGradingEquivSectionsTwist_symm,
    awayToLocalization_map_psi 𝒜 d hf,
    Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_smul]
  rfl

end Stacks.Truncation

namespace Stacks.AlgebraicGeometry.ProjConeTwist

open Stacks.Truncation

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A}

/-- The module structure on the sections of a twisting sheaf over the sections of the structure
sheaf, read as a sheaf of rings. -/
local instance instTwistSectionsModule (m : ℤ) (U : (TopologicalSpace.Opens
      (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module (((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj U)
      ((ProjectiveSpectrum.Proj.modulePresheaf 𝒜 (twistGrading 𝒜 m)).obj U) :=
  ((twistingSheaf 𝒜 m).val.obj U).isModule

/-- The graded ring homomorphism of the truncation cone data is `ψ`. -/
theorem truncationConeData_psi : (truncationConeData 𝒜).psi = psi 𝒜 := rfl

/-- The scheme-level and the homogeneous-spectrum-level names for the canonical map
`A₍f₎ ⟶ Γ(P, D₊(f))` agree. -/
theorem awayToSection_eq (f : A) :
    AlgebraicGeometry.Proj.awayToSection 𝒜 f =
      ProjectiveSpectrum.Proj.awayToSection 𝒜 f := rfl

/-- On a standard open of a positive-degree homogeneous element every section of the structure
sheaf is a degree-zero fraction. -/
theorem awayToSection_surjective {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Function.Surjective (AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom := by
  have hiso : IsIso (AlgebraicGeometry.Proj.awayToSection 𝒜 f) := by
    rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom 𝒜 f hf hd]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso (AlgebraicGeometry.Proj.awayToSection 𝒜 f)).2

/-- Transporting the sections over `D₊(ψ f)` back along `π⁻¹(D₊(f)) = D₊(ψ f)` undoes the
inequality of opens that `AlgebraicGeometry.Scheme.Hom.appLE` carries. -/
theorem pi_app_eq (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (pi 𝒜).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f)
        (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 f))
        (pi_preimage_basicOpen 𝒜 f d hf hd).ge ≫
      (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
        (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op =
      (pi 𝒜).app (AlgebraicGeometry.Proj.basicOpen 𝒜 f) := by
  rw [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp,
    show ((homOfLE (pi_preimage_basicOpen 𝒜 f d hf hd).ge).op ≫
        (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op) =
      CategoryStruct.id _ from Subsingleton.elim _ _]
  simp

/-- The cone projection on functions over a standard open: the image of a degree-zero fraction of
`A` under `ψ`, read as a function on `D₊(ψ f)` and transported along `π⁻¹(D₊(f)) = D₊(ψ f)`, is
the pullback of that fraction along `π`. -/
@[stacks 0EKG "the cone projection on functions over a standard open, with the sections over \
D+(psi f) transported along the identity of opens pi^{-1}(D+(f)) = D+(psi f)"]
theorem awayToSection_pi_app (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (r : HomogeneousLocalization.Away 𝒜 f) :
    (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
        (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom
          (HomogeneousLocalization.Away.map (psi 𝒜) f r)) =
      ((pi 𝒜).app (AlgebraicGeometry.Proj.basicOpen 𝒜 f)).hom
        ((AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom r) := by
  have h := Stacks.AlgebraicGeometry.ProjAndSpec.awayToSection_comp_pi_appLE
    (truncationConeData 𝒜) hd hf
  have h1 : (AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom
        (HomogeneousLocalization.Away.map (psi 𝒜) f r) =
      ((pi 𝒜).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f)
        (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 f))
        (pi_preimage_basicOpen 𝒜 f d hf hd).ge).hom
        ((AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom r) := by
    have h2 := ConcreteCategory.congr_hom h.symm r
    simp only [truncationConeData_psi] at h2
    exact h2
  rw [h1, ← CommRingCat.comp_apply, pi_app_eq 𝒜 d hf hd]

/-- The degreewise inclusion `Γ(D₊(f), 𝒪_P(m)) → (B[1/ψ f])₀`, as an additive map: the
inverse of `Stacks.Truncation.awayGradingEquivSectionsTwist` followed by the inclusion of the
degree-`m` summand. -/
@[stacks 0EKG "the degreewise inclusion of the sections of O_P(m) over D+(f) into the \
degree-zero localization of the truncation algebra, as an additive map"]
def coneTwistAwayHom (m d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    ((twistingSheaf 𝒜 (m : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) →+
      HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f) :=
  (AddSubgroup.subtype (awayGrading 𝒜 d hf m)).comp
    (awayGradingEquivSectionsTwist 𝒜 d hf hd m).symm.toAddMonoidHom

/-- `coneTwistAwayHom 𝒜 m d hf hd s` is the inverse of
`Stacks.Truncation.awayGradingEquivSectionsTwist` applied to `s`, read in `(B[1/ψ f])₀`. -/
@[simp] theorem coneTwistAwayHom_apply (m d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (s : (twistingSheaf 𝒜 (m : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    coneTwistAwayHom 𝒜 m d hf hd s =
      (((awayGradingEquivSectionsTwist 𝒜 d hf hd m).symm s :
        HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f))) :=
  rfl

/-- The local degreewise inclusion `Γ(D₊(f), 𝒪_P(m)) ⟶ Γ(D₊(f), π_* 𝒪_L)`, as a morphism of
modules over the sections of `𝒪_P` on `D₊(f)`. -/
@[stacks 0EKG "the degreewise inclusion O_P(m) to pi_* O_L over one standard open D+(f), as a \
map of modules over the sections of O_P there"]
def coneTwistApp (m d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (twistingSheaf 𝒜 (m : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.obj
        (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f)) := by
  letI iN : Module (((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
      ((Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.obj
        (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f))) :=
    ((Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.obj
      (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f))).isModule
  let L : ((twistingSheaf 𝒜 (m : ℤ)).val.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f))) →ₗ[
      (((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)))]
      ((Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.obj
        (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f))) :=
    { toFun := fun s => (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
          (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op
          ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom
            (coneTwistAwayHom 𝒜 m d hf hd s))
      map_add' := by
        intro s t
        refine Eq.trans (congrArg (fun z => (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
            (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op
            ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom z))
          (map_add (coneTwistAwayHom 𝒜 m d hf hd) s t)) ?_
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro r s
        obtain ⟨a, rfl⟩ := awayToSection_surjective 𝒜 hf hd r
        refine Eq.trans (congrArg (fun z => (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
            (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op
            ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom z))
          (awayGradingEquivSectionsTwist_symm_smul 𝒜 d hf hd m a s)) ?_
        rw [map_mul, map_mul, awayToSection_pi_app 𝒜 d hf hd]
        rfl }
  exact @ModuleCat.ofHom _ _ _ _ _ _ _ iN L

/-- The components of the local map: a section of `𝒪_P(m)` over `D₊(f)` goes to its degreewise
inclusion into `(B[1/ψ f])₀`, read as a function on `D₊(ψ f)` and transported along
`π⁻¹(D₊(f)) = D₊(ψ f)`. -/
theorem coneTwistApp_apply (m d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (s : (twistingSheaf 𝒜 (m : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (coneTwistApp 𝒜 m d hf hd).hom s =
      (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
        (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom
          (coneTwistAwayHom 𝒜 m d hf hd s)) :=
  rfl

end Stacks.AlgebraicGeometry.ProjConeTwist

end
