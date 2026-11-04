module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Trivialization
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.TwistSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveLine.FormPowerFactor
public import StacksFrontier.AlgebraicGeometry.ProjectiveLine.Complement

/-!
# A trivialization of a twist on a standard open of `ℙ¹_k`, read as a divisibility

Let `k` be a field and let `f ∈ k[T₀, T₁]` be homogeneous of degree `d > 0`. A trivialization of
the twist `𝒪(t)` over the standard open `D₊(f)` is the same thing as a *generator* of its
sections there — a section `s` such that multiplication by `s` is bijective
`𝒪(V) → 𝒪(t)(V)` for every `V ⊆ D₊(f)` — and the sections of `𝒪(t)` over `D₊(f)` are the single
fractions `x / f ʲ` with `x` homogeneous of degree `j d + t`. Writing the generator as `h / f ⁿ`,
every such `x` satisfies `h ∣ x f ᴺ` for some `N`.

## Main results

* `Stacks.ProjectiveLine.surjective_awayToSection`: the degree-zero localization `A₍f₎` maps onto
  the ring of functions on `D₊(f)`.
* `Stacks.ProjectiveLine.exists_dvd_of_generatorSections`: a generator of `𝒪(t)` over `D₊(f)`
  gives a form `h` of degree `n d + t` with `h ∣ x f ᴺ`, for every `x` homogeneous of degree
  `j d + t` and some `N`.

## References

* [Stacks Project, Tag 0CDP](https://stacks.math.columbia.edu/tag/0CDP)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjectiveCohomology
open Stacks.SheafOfModules

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjectiveLine

universe u

variable {k : Type u} [Field k]

/-- For a homogeneous form `f` of positive degree, the map from the degree-zero localization
at `f` to the ring of functions on the standard open `D₊(f)` is surjective. -/
theorem surjective_awayToSection {dF : ℕ} {f : MvPolynomial (Fin 2) k} (hf : f ∈ grading k dF)
    (hdF : 0 < dF) :
    Function.Surjective
      (AlgebraicGeometry.Proj.awayToSection (grading k) f).hom := by
  have hiso : IsIso (AlgebraicGeometry.Proj.awayToSection (grading k) f) := by
    rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom (grading k) f hf hdF]
    infer_instance
  exact ((ConcreteCategory.isIso_iff_bijective
    (AlgebraicGeometry.Proj.awayToSection (grading k) f)).mp hiso).surjective

/-- **A generator of `𝒪(t)` on `D₊(f)` gives a divisibility in `k[T₀, T₁]`.** For `f`
homogeneous of positive degree, given a generator of `𝒪(t)` over `D₊(f)`, there are `n` and
`h` homogeneous of degree `n deg f + t` such that for every `x` homogeneous of degree
`j deg f + t` there is `N` with `h ∣ x f ᴺ`. -/
theorem exists_dvd_of_generatorSections {dF : ℕ} {f : MvPolynomial (Fin 2) k}
    (hf : f ∈ grading k dF) (hdF : 0 < dF) (t : ℤ)
    (s : GeneratorSections (AlgebraicGeometry.Proj (grading k)).toRingedSpace
      (associatedModuleSheaf (grading k)
        (twistGrading (S := MvPolynomial (Fin 2) k) (grading k) t))
      (ProjectiveSpectrum.basicOpen (grading k) f)) :
    ∃ (n : ℕ) (h : MvPolynomial (Fin 2) k),
      h ∈ integerGrading (S := MvPolynomial (Fin 2) k) (grading k) (((n * dF : ℕ) : ℤ) + t) ∧
      ∀ (j : ℕ) (x : MvPolynomial (Fin 2) k),
        x ∈ integerGrading (S := MvPolynomial (Fin 2) k) (grading k) (((j * dF : ℕ) : ℤ) + t) →
        ∃ N : ℕ, h ∣ x * f ^ N := by
  classical
  let inst := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := MvPolynomial (Fin 2) k) f (MvPolynomial (Fin 2) k))
    (algebraMap (HomogeneousLocalization.Away (grading k) f) (Localization.Away f))
  have hself := Stacks.SheafOfModules.generator_restrict_self
    (X := (AlgebraicGeometry.Proj (grading k)).toRingedSpace)
    (associatedModuleSheaf (grading k)
      (twistGrading (S := MvPolynomial (Fin 2) k) (grading k) t))
    (ProjectiveSpectrum.basicOpen (grading k) f) s
  have hsurj := (s.property (ProjectiveSpectrum.basicOpen (grading k) f) le_rfl).surjective
  simp only [hself] at hsurj
  have E : ↑((associatedModuleSheaf (grading k)
        (twistGrading (S := MvPolynomial (Fin 2) k) (grading k) t)).val.obj
        (op (ProjectiveSpectrum.basicOpen (grading k) f)))
      ≃ₗ[HomogeneousLocalization.Away (grading k) f]
      ↥(GradedModuleDegreeZeroLocalization (grading k)
        (twistGrading (S := MvPolynomial (Fin 2) k) (grading k) t) f) :=
    associatedModuleSheafStandardOpenEquiv (grading k)
      (twistGrading (S := MvPolynomial (Fin 2) k) (grading k) t) hf hdF
  obtain ⟨n, h, hh, hgen⟩ := (mem_awayGrading (grading k)).mp
    ((mem_degreeZeroLocalization_twistGrading_iff (grading k) hf t _).mp (E s.val).2)
  refine ⟨n, h, hh, fun j x hx => ?_⟩
  have hz : (LocalizedModule.mk x ⟨f ^ j, ⟨j, rfl⟩⟩ :
        LocalizedModule.Away f (MvPolynomial (Fin 2) k)) ∈
      GradedModuleDegreeZeroLocalization (grading k)
        (twistGrading (S := MvPolynomial (Fin 2) k) (grading k) t) f :=
    (mem_degreeZeroLocalization_twistGrading_iff (grading k) hf t _).mpr
      ((mem_awayGrading (grading k)).mpr ⟨j, x, hx, rfl⟩)
  obtain ⟨r, hr⟩ := hsurj (E.symm ⟨_, hz⟩)
  obtain ⟨a, rfl⟩ := surjective_awayToSection hf hdF r
  obtain ⟨i, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading k) hf a
  have hkey : (⟨_, hz⟩ : GradedModuleDegreeZeroLocalization (grading k)
      (twistGrading (S := MvPolynomial (Fin 2) k) (grading k) t) f) =
      HomogeneousLocalization.Away.mk (grading k) hf i p hp • E s.val := by
    refine E.symm.injective (hr.symm.trans ?_)
    exact ((map_smul E.symm (HomogeneousLocalization.Away.mk (grading k) hf i p hp)
      (E s.val)).trans (congrArg
        (fun w => HomogeneousLocalization.Away.mk (grading k) hf i p hp • w)
        (E.symm_apply_apply s.val))).symm
  have hval : (LocalizedModule.mk x ⟨f ^ j, ⟨j, rfl⟩⟩ :
        LocalizedModule.Away f (MvPolynomial (Fin 2) k)) =
      LocalizedModule.mk (p • h)
        (⟨f ^ i * f ^ n, ⟨i + n, by simp [pow_add]⟩⟩ : ↥(Submonoid.powers f)) := by
    have hsm : (HomogeneousLocalization.Away.mk (grading k) hf i p hp •
          (LocalizedModule.mk h ⟨f ^ n, ⟨n, rfl⟩⟩ :
            LocalizedModule.Away f (MvPolynomial (Fin 2) k))) =
        Localization.mk p (⟨f ^ i, ⟨i, rfl⟩⟩ : ↥(Submonoid.powers f)) •
          (LocalizedModule.mk h ⟨f ^ n, ⟨n, rfl⟩⟩ :
            LocalizedModule.Away f (MvPolynomial (Fin 2) k)) := rfl
    have h1 := congrArg Subtype.val hkey
    rw [Submodule.coe_smul, hgen, hsm] at h1
    exact h1.trans (LocalizedModule.mk_smul_mk p h _ _)
  obtain ⟨⟨_, cN, rfl⟩, hcc⟩ := LocalizedModule.mk_eq.mp hval
  refine ⟨cN + (i + n), ⟨f ^ cN * f ^ j * p, ?_⟩⟩
  simp only [Submonoid.smul_def, smul_eq_mul] at hcc
  calc x * f ^ (cN + (i + n)) = f ^ cN * (f ^ i * f ^ n * x) := by ring
    _ = f ^ cN * (f ^ j * (p * h)) := by rw [hcc]
    _ = h * (f ^ cN * f ^ j * p) := by ring

end Stacks.ProjectiveLine

end
