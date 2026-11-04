module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.TwistSections

/-!
# The scalar action in the standard-open description of an associated module sheaf

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `M = ⨁_{i ∈ ℤ} 𝒨 i` a graded `A`-module and `f ∈ 𝒜 d`
homogeneous of positive degree. The sections of the associated sheaf `M̃` over the standard open
`D₊(f)` are the degree-zero localization `M₍f₎`, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`, and that
identification is linear over the degree-zero localization `A₍f₎` of the ring. On the underlying
elements of `M_f`, the action of `A₍f₎` is multiplication by the fraction `r.val ∈ A_f`:

  `(φ (awayToSection f r • s)).val = r.val • (φ s).val`.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.standardOpenModule_smul`: the `A₍f₎`-action on the
  sections over `D₊(f)` is the action of the corresponding section of the structure sheaf.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.coe_smul_gradedModuleDegreeZeroLocalization`: the
  `A₍f₎`-action on `M₍f₎` is multiplication by the underlying fraction.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.coe_associatedModuleSheafStandardOpenEquiv_smul`:
  the standard-open identification `Γ(D₊(f), M̃) = M₍f₎` carries the action of
  `Γ(P, D₊(f))` through `Proj.awayToSection` to multiplication by the fraction.
* `Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_smul`: the same for the
  identification of `Γ(D₊(f), 𝒪_P(m))` with the degree-`m` part of `A_f`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv_degree_indep`:
  the standard-open identification depends only on the standard open, not on the degree in
  which the element cutting it out is homogeneous.

## References

* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u v w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The grading action used for a naturally graded ring acting on an integer-graded module. -/
local instance : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

omit [DirectSum.Decomposition 𝒨] in
/-- The action of the degree-zero localization `A₍f₎` on the sections of `M̃` over the standard
open `D₊(f)` is the action of the section of the structure sheaf that `A₍f₎` names. -/
theorem standardOpenModule_smul (f : S) (r : HomogeneousLocalization.Away 𝒜 f)
    (s : moduleSections 𝒜 𝒨 (ProjectiveSpectrum.basicOpen 𝒜 f)) :
    r • s = (ProjectiveSpectrum.Proj.awayToSection 𝒜 f).hom r • s :=
  rfl

/-- The action of `A₍f₎` on the degree-zero localization `M₍f₎` is multiplication of the
underlying element of `M_f` by the underlying fraction. -/
theorem coe_smul_gradedModuleDegreeZeroLocalization (f : S)
    (r : HomogeneousLocalization.Away 𝒜 f)
    (z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) :
    ((r • z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) : LocalizedModule.Away f M) =
      HomogeneousLocalization.val r • (z : LocalizedModule.Away f M) :=
  rfl

/-- The standard-open identification `Γ(D₊(f), M̃) = M₍f₎` is linear for the action of
`Γ(P, D₊(f))` read through `AlgebraicGeometry.Proj.awayToSection`, the action on the target being
multiplication by the fraction inside `M_f`. -/
@[stacks 01M6 "part (3), the scalar action in the standard-open identification, written out on \
the underlying elements of the localization"]
theorem coe_associatedModuleSheafStandardOpenEquiv_smul {f : S} {d : ℕ} (hf : f ∈ 𝒜 d)
    (hd : 0 < d) (r : HomogeneousLocalization.Away 𝒜 f)
    (s : (associatedModuleSheaf 𝒜 𝒨).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    ((associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd
          ((ProjectiveSpectrum.Proj.awayToSection 𝒜 f).hom r • s) :
        LocalizedModule.Away f M)) =
      HomogeneousLocalization.val r •
        ((associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd s : LocalizedModule.Away f M)) :=
  congrArg Subtype.val (map_smul (associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd) r s)

/-- The standard-open identification is a two-sided inverse of the comparison
`M₍f₎ → Γ(D₊(f), M̃)`: applying the comparison to it returns the section. -/
theorem degreeZeroToSection_associatedModuleSheafStandardOpenEquiv {f : S} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (s : (associatedModuleSheaf 𝒜 𝒨).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    degreeZeroToSection 𝒜 𝒨 f (associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd s) = s :=
  (LinearEquiv.ofBijective (degreeZeroToSection 𝒜 𝒨 f)
    ⟨degreeZeroToSection_injective 𝒜 𝒨 hf hd,
      degreeZeroToSection_surjective 𝒜 𝒨 hf hd⟩).apply_symm_apply s

/-- The standard-open identification depends only on the standard open, not on the degree in
which the element defining it is homogeneous. -/
theorem associatedModuleSheafStandardOpenEquiv_degree_indep {f : S} {d d' : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) (hf' : f ∈ 𝒜 d') (hd' : 0 < d')
    (s : (associatedModuleSheaf 𝒜 𝒨).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd s =
      associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf' hd' s :=
  degreeZeroToSection_injective 𝒜 𝒨 hf hd
    ((degreeZeroToSection_associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd s).trans
      (degreeZeroToSection_associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf' hd' s).symm)

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.ProjectiveCohomology

open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {k : ℕ}

/-- The identification of `Γ(D₊(f), 𝒪_P(m))` with the degree-`m` part of `A_f` is linear for
the action of `Γ(P, D₊(f))` read through `AlgebraicGeometry.Proj.awayToSection`: a section
scaled by the fraction `r` has for underlying element the product of `r.val` with the underlying
element of the section. -/
@[stacks 01MN "part (1), the scalar action in the standard-open description of the sections of \
a twist, written out on the underlying elements of the localization"]
theorem coe_sectionsTwistEquivAwayGrading_smul (hf : f ∈ 𝒜 k) (hk : 0 < k) (m : ℤ)
    (r : HomogeneousLocalization.Away 𝒜 f)
    (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    ((sectionsTwistEquivAwayGrading 𝒜 hf hk m
        ((ProjectiveSpectrum.Proj.awayToSection 𝒜 f).hom r • s) :
      LocalizedModule.Away f A)) =
      HomogeneousLocalization.val r •
        ((sectionsTwistEquivAwayGrading 𝒜 hf hk m s : LocalizedModule.Away f A)) := by
  rw [coe_sectionsTwistEquivAwayGrading, coe_sectionsTwistEquivAwayGrading]
  exact coe_associatedModuleSheafStandardOpenEquiv_smul 𝒜 _ hf hk r s

end Stacks.ProjectiveCohomology

end
