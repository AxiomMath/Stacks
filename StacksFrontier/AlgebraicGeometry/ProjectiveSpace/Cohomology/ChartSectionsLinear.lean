module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism
public import StacksFrontier.RingTheory.HomogeneousLocalization.BaseAlgebra

/-!
# The monomial chart is the module of sections of `𝒪(d)` over the coefficient ring

Let `R` be a commutative ring and let `P = R[T₀, …, Tₙ]` carry its grading by total degree, so
that `ℙⁿ_R = Proj P`. A coefficient `r : R` pulls back along the structure morphism
`ℙⁿ_R ⟶ Spec R` to a global section of `𝒪_{ℙⁿ_R}`, and multiplication by that section is the
`R`-action on the sections of the twisting sheaf `𝒪(d)`. This file identifies that action, over
the standard open `D₊(∏_{i ∈ s} Tᵢ)`, with the `R`-action on the free module
`Stacks.ProjectiveSpace.Cohomology.twistChart` on the degree-`d` Laurent monomials: the additive
identification `Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquivTwistChart` is `R`-linear.

The bridge is that the pulled-back section restricts on a standard open `D₊(f)` to the image of
`r` in the degree-zero localization `P₍f₎` under
`AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection`, both being the constant fraction
`C r / 1` in every fibre. The comparison of the sections on `D₊(f)` with `P₍f₎` is already
`P₍f₎`-linear by [Stacks, Tag 01M6], so the coefficients are carried along by the structure map
`R → P₍f₎`.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.coeffToGlobalSections` — the ring homomorphism from the
  coefficients to the global sections of `𝒪_{ℙⁿ_R}` given by the structure morphism.
* `Stacks.ProjectiveSpace.Cohomology.coeffToChartSections` — the same, restricted to the standard
  open `D₊(∏_{i ∈ s} Tᵢ)`.
* `Stacks.ProjectiveSpace.Cohomology.chartSheafSectionsModule` — the sections of `𝒪(d)` over a
  standard open as a module over the ring of sections of `𝒪` there.
* `Stacks.ProjectiveSpace.Cohomology.chartSheafSectionsBaseModule` — those sections as an
  `R`-module, through the degree-zero localization.
* `Stacks.ProjectiveSpace.Cohomology.chartSectionsLinearEquivTwistChart` — the identification of
  the sections with the monomial chart, as an `R`-linear equivalence.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.res_coeffToGlobalSections` — **the key compatibility**: on a
  standard open `D₊(f)` the pullback of `r : R` is `awayToSection` of the image of `r` in `P₍f₎`.
* `Stacks.ProjectiveSpace.Cohomology.coeffToChartSections_smul` — hence multiplication by that
  pulled-back section is the `R`-action of
  `Stacks.ProjectiveSpace.Cohomology.chartSheafSectionsBaseModule`.
* `Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquivTwistChart_smul` — **the payoff**:
  through the identification of the sections of `𝒪(d)` over `D₊(∏_{i ∈ s} Tᵢ)` with the monomial
  chart, multiplication by the pullback of `r` is multiplication by `r` on Laurent coefficients.
* `Stacks.ProjectiveSpace.Cohomology.coe_chartSectionsLinearEquivTwistChart` — the `R`-linear
  identification has the same underlying function as the additive one.

## Implementation notes

The `R`-action on the sections is supplied as a `def` rather than as an instance: a global
`Module R` instance on the sections would meet the `R`-algebra structure of
`Stacks.SymmetricAway.algebraChartRing` on the same carrier by a second path. A consumer that
wants it supplies it with `letI`, which is also how the type of
`Stacks.ProjectiveSpace.Cohomology.chartSectionsLinearEquivTwistChart` names it.

The action of the ring of sections of `𝒪` is an instance, because nothing else provides it: the
module structure carried by the twisting sheaf is stated over the image of that ring under
`CategoryTheory.forget₂ CommRingCat RingCat`, which instance search does not see through.

The restriction of `Stacks.ProjectiveSpace.Cohomology.coeffToGlobalSections` to a standard open
is given a name of its own because its source, the global sections of `𝒪_{ℙⁿ_R}`, is spelled
through the scheme `Proj P` while the restriction map is spelled through
`AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf`; identifying the two is a definitional
unfolding that is done once here rather than inside every statement.

## References

* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory TopologicalSpace
  Opposite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

/-! ### The coefficients as sections of the structure sheaf -/

/-- **The coefficients as global functions on projective space.** The ring homomorphism
`R → Γ(ℙⁿ_R, 𝒪)` obtained from the structure morphism `ℙⁿ_R ⟶ Spec R` of
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff` by identifying `R` with the global
sections of `Spec R`. -/
def coeffToGlobalSections (R : Type u) [CommRing R] (n : ℕ) :
    R →+* Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n).appTop).hom

section Restriction

variable {R : Type u} [CommRing R] {n : ℕ} {f : MvPolynomial (Fin (n + 1)) R}

/-- **The pullback of a coefficient on a standard open.** Restricting the global section
`coeffToGlobalSections R n r` to `D₊(f)` gives the image of `r` under the structure map
`R → P₍f₎` of the degree-zero localization, read as a section by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection`. Both sections have the constant value
`C r / 1` in every fibre, so they agree there; no homogeneity of `f` is used. -/
theorem res_coeffToGlobalSections (r : R) :
    (ProjectiveSpectrum.Proj.structureSheaf _).obj.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen _ f ≤ ⊤)).op
        (coeffToGlobalSections R n r)
      = ProjectiveSpectrum.Proj.awayToSection _ f
          (algebraMap R (HomogeneousLocalization.Away _ f) r) := by
  refine Subtype.ext (funext fun p => HomogeneousLocalization.val_injective _ ?_)
  refine Eq.trans
    (Stacks.AlgebraicGeometry.ProjEulerSequence.projToSpecCoeff_appTop_val R n r p.1) ?_
  refine Eq.trans ?_ (ProjectiveSpectrum.Proj.awayToSection_apply
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) f
    (algebraMap R (HomogeneousLocalization.Away _ f) r) p).symm
  rw [HomogeneousLocalization.val_algebraMap,
    IsScalarTower.algebraMap_apply R (MvPolynomial (Fin (n + 1)) R) (Localization.Away f),
    MvPolynomial.algebraMap_eq]
  exact Eq.trans rfl (IsLocalization.map_eq (M := Submonoid.powers f)
    (S := Localization.Away f) (g := RingHom.id (MvPolynomial (Fin (n + 1)) R)) _
    (MvPolynomial.C r)).symm

end Restriction

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (s : Finset (Fin (n + 1)))

/-- **The coefficients as functions on a standard open.** The restriction of
`coeffToGlobalSections R n` to `D₊(∏_{i ∈ s} Tᵢ)`. -/
def coeffToChartSections :
    R →+* (ProjectiveSpectrum.Proj.structureSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).obj.obj
          (op (ProjectiveSpectrum.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n s))) :=
  ((ProjectiveSpectrum.Proj.structureSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).obj.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n s) ≤ ⊤)).op).hom.comp
    (coeffToGlobalSections R n)

/-- `res_coeffToGlobalSections` for the chart denominator: the coefficient `r`, as a function on
`D₊(∏_{i ∈ s} Tᵢ)`, is the image of `r` in the degree-zero localization there. -/
theorem coeffToChartSections_apply (r : R) :
    coeffToChartSections R n s r
      = ProjectiveSpectrum.Proj.awayToSection _ (chartDenom R n s)
          (algebraMap R (HomogeneousLocalization.Away _ (chartDenom R n s)) r) :=
  res_coeffToGlobalSections r

/-! ### The two scalar actions on the sections over a chart -/

/-- **The sections of `𝒪` act on the sections of `𝒪(d)`.** The action of the ring
`Γ(D₊(∏_{i ∈ s} Tᵢ), 𝒪)` on the sections of the twisting sheaf over that standard open; it is the
pointwise action of `AlgebraicGeometry.ProjectiveSpectrum.Proj.modulePresheafModule`. -/
instance chartSheafSectionsModule :
    Module ((ProjectiveSpectrum.Proj.structureSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).obj.obj
          (op (ProjectiveSpectrum.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n s))))
      (chartSheafSections R n d s) :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.modulePresheafModule _ _ _

/-- The action of the degree-zero localization on the sections over a standard open is the action
of the ring of sections of `𝒪` there, transported along
`AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection`. -/
theorem awayToSection_smul (c : HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n s))
    (x : chartSheafSections R n d s) :
    ProjectiveSpectrum.Proj.awayToSection _ (chartDenom R n s) c • x = c • x := rfl

/-- **The coefficients act on the sections of `𝒪(d)` over a chart.** The `R`-module structure
obtained from the action of the degree-zero localization `P₍∏_{i ∈ s} Tᵢ₎` along its structure
map `R → P₍∏_{i ∈ s} Tᵢ₎`. -/
@[instance_reducible]
def chartSheafSectionsBaseModule : Module R (chartSheafSections R n d s) :=
  Module.compHom _ (algebraMap R (HomogeneousLocalization.Away
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n s)))

/-- **Multiplying by a pulled-back coefficient is the `R`-action.** On the sections of `𝒪(d)`
over `D₊(∏_{i ∈ s} Tᵢ)` the action of `coeffToChartSections R n s r` is the scalar action of `r`
given by `chartSheafSectionsBaseModule`. -/
theorem coeffToChartSections_smul (r : R) (x : chartSheafSections R n d s) :
    letI := chartSheafSectionsBaseModule R n d s
    coeffToChartSections R n s r • x = r • x :=
  congrArg (fun g => g • x) (coeffToChartSections_apply R n s r)

/-! ### `R`-linearity of the monomial model -/

/-- The image of a coefficient in the degree-zero localization acts on the localization
`P[1/∏_{i ∈ s} Tᵢ]` as the coefficient itself: it is the fraction `C r / 1`. -/
theorem val_algebraMap_smul (r : R)
    (z : LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) :
    (algebraMap R (HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n s)) r).val • z
      = r • z := by
  rw [HomogeneousLocalization.val_algebraMap]
  exact IsScalarTower.algebraMap_smul _ r z

/-- The fraction representing a section is linear over the degree-zero localization: the
comparison `Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquiv` is the underlying map of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`, which is
`P₍∏_{i ∈ s} Tᵢ₎`-linear. -/
theorem coe_chartSectionsAddEquiv_smul (hs : s.Nonempty)
    (c : HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n s))
    (x : chartSheafSections R n d s) :
    ((chartSectionsAddEquiv R n d s hs (c • x) : twistSections R n d s) :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))
      = c.val • ((chartSectionsAddEquiv R n d s hs x : twistSections R n d s) :
          LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) :=
  congrArg Subtype.val
    (map_smul (AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d)
      (chartDenom_mem_homogeneousSubmodule n s) (Finset.card_pos.2 hs)) c x)

/-- **The graded-piece model is `R`-linear.** A coefficient `r`, acting through the degree-zero
localization, becomes the `R`-action on the degree-`d` part of `P[1/∏_{i ∈ s} Tᵢ]`. -/
theorem chartSectionsAddEquiv_algebraMap_smul (hs : s.Nonempty) (r : R)
    (x : chartSheafSections R n d s) :
    chartSectionsAddEquiv R n d s hs
        ((algebraMap R (HomogeneousLocalization.Away
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n s)) r) • x)
      = r • chartSectionsAddEquiv R n d s hs x :=
  Subtype.ext ((coe_chartSectionsAddEquiv_smul R n d s hs
      (algebraMap R (HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n s)) r) x).trans
    (val_algebraMap_smul R n s r _))

/-- **The monomial model is `R`-linear**, with the scalars taken in the degree-zero
localization. -/
theorem chartSectionsAddEquivTwistChart_algebraMap_smul (hs : s.Nonempty) (r : R)
    (x : chartSheafSections R n d s) :
    chartSectionsAddEquivTwistChart R n d s hs
        ((algebraMap R (HomogeneousLocalization.Away
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n s)) r) • x)
      = r • chartSectionsAddEquivTwistChart R n d s hs x :=
  (congrArg (fun w : twistSections R n d s => (twistChartEquivTwistSections R n d s).symm w)
    (chartSectionsAddEquiv_algebraMap_smul R n d s hs r x)).trans (map_smul _ r _)

/-- **The monomial model of the sections of `𝒪(d)` is linear over the coefficients.** Let `g r`
be the restriction to `D₊(∏_{i ∈ s} Tᵢ)` of the global section of `𝒪_{ℙⁿ_R}` that `r : R` pulls
back to along the structure morphism. Through the identification of the sections of `𝒪(d)` with
the monomial chart, multiplication by `g r` is multiplication by `r` on the Laurent
coefficients. -/
theorem chartSectionsAddEquivTwistChart_smul (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) (r : R) (x : chartSheafSections R n d s) :
    chartSectionsAddEquivTwistChart R n d s hs (coeffToChartSections R n s r • x)
      = r • chartSectionsAddEquivTwistChart R n d s hs x :=
  (congrArg (fun g => chartSectionsAddEquivTwistChart R n d s hs (g • x))
      (coeffToChartSections_apply R n s r)).trans
    (chartSectionsAddEquivTwistChart_algebraMap_smul R n d s hs r x)

/-- **The monomial chart is the module of sections of `𝒪(d)`, `R`-linearly.** The additive
identification `Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquivTwistChart` of the sections
of `𝒪(d)` over `D₊(∏_{i ∈ s} Tᵢ)` with the free `R`-module on the degree-`d` Laurent monomials
regular outside `s` is linear for the `R`-action of
`Stacks.ProjectiveSpace.Cohomology.chartSheafSectionsBaseModule`, which by
`Stacks.ProjectiveSpace.Cohomology.coeffToChartSections_smul` is multiplication by the section
that `r` pulls back to along the structure morphism. -/
def chartSectionsLinearEquivTwistChart (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    letI := chartSheafSectionsBaseModule R n d s
    chartSheafSections R n d s ≃ₗ[R] twistChart R n d (↑s : Set (Fin (n + 1))) :=
  letI := chartSheafSectionsBaseModule R n d s
  { toFun := chartSectionsAddEquivTwistChart R n d s hs
    map_add' := (chartSectionsAddEquivTwistChart R n d s hs).map_add
    map_smul' := chartSectionsAddEquivTwistChart_algebraMap_smul R n d s hs
    invFun := (chartSectionsAddEquivTwistChart R n d s hs).symm
    left_inv := (chartSectionsAddEquivTwistChart R n d s hs).left_inv
    right_inv := (chartSectionsAddEquivTwistChart R n d s hs).right_inv }

/-- The `R`-linear identification of the sections with the monomial chart has the same underlying
function as the additive one. -/
theorem coe_chartSectionsLinearEquivTwistChart (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    letI := chartSheafSectionsBaseModule R n d s
    ⇑(chartSectionsLinearEquivTwistChart R n d s hs)
      = ⇑(chartSectionsAddEquivTwistChart R n d s hs) := rfl

end Stacks.ProjectiveSpace.Cohomology

end
