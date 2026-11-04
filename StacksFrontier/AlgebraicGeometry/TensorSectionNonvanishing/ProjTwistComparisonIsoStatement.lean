module

public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistChartBijective

/-!
# A quasi-coherent sheaf on `ℙᵐ_R` is the sheaf associated to its twisted global sections

Let `R` be a ring and let `ℱ` be a quasi-coherent sheaf on `ℙᵐ_R = Proj R[T₀, …, Tₘ]`. For
`d ≥ 0` put `M_d = Γ(ℙᵐ_R, ℱ(d))`. This file states [Stacks, Tag 03GM] as a single theorem:
`M = ⨁_{d ≥ 0} M_d` is a graded `R[T₀, …, Tₘ]`-module, and the canonical comparison `M̃ ⟶ ℱ` is
an isomorphism.

## The statement

The graded-module half is the conjunction of three facts about the structure the library
attaches to `M`: the integer grading `moduleGrading` decomposes `M` internally
(`DirectSum.IsInternal`), the grading of `R[T₀, …, Tₘ]` acts on it
(`SetLike.GradedSMul`), and the action of a homogeneous `a` on a homogeneous section is the
multiplication map of the twists, `Stacks.AlgebraicGeometry.ProjTwistSectionModule.gsmul`, which
comes from the natural isomorphisms `𝒪(e) ⊗ ℱ(d) ⟶ ℱ(e + d)` of Equation 03GK. Together these
say that `M` is a graded module over the graded ring, with the grading and the action the
source's.

The isomorphism half is the conjunction of the uniqueness that makes the comparison canonical --
it is the only morphism `M̃ ⟶ ℱ` restricting on each positive-degree standard open `D₊(f)` to
`x / f ^ n ↦ x|_{D₊(f)} ⊗ f ^ (-n)` -- and its invertibility.

## How the isomorphism is obtained

The source writes `ℱ|_{U_i} = Ñ_i` on the charts of the degree-one coordinates and omits the
injectivity and surjectivity arguments. Those two arguments are
`Stacks.AlgebraicGeometry.ProjTwistChartBijective.exists_pow_smul_eq_zero_of_numerSection_eq_zero`
and `Stacks.AlgebraicGeometry.ProjTwistChartBijective.exists_numerSection_eq`; they give
bijectivity of the chart comparison at every positive-degree homogeneous element
(`isIso_comparison_of_degreeOneCover`), which the gluing principle
`Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery.isIso_of_bijective_app_onBasis` turns into
invertibility of `M̃ ⟶ ℱ`. The finite cover they need is the `m + 1` coordinate charts, indexed
here in the universe of `R` because the gluing axiom for sheaves on `Proj` quantifies over index
types in the universe of the space.

## Caveats

* The grading of `R[T₀, …, Tₘ]` is by **total degree**
  (`Stacks.AlgebraicGeometry.ProjTwistSectionModule.projectiveGrading`), as the source's
  `ℙᵐ_R` requires.
* `ℱ` is a sheaf of modules over the sheaf of rings
  `Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf`, which is the sheaf of rings of
  the scheme `ℙᵐ_R`; quasi-coherence is therefore stated at the scheme's spelling of that sheaf
  of rings, `(Proj 𝒮).ringCatSheaf`, the two being the same object.
* The source writes the isomorphism as `ℱ = M̃`; what is proved is invertibility of the
  comparison morphism `M̃ ⟶ ℱ`, which is the same statement in either direction.

## References

* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section
open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistSectionModule
open Stacks.AlgebraicGeometry.ProjTwistLocalComparison
open Stacks.AlgebraicGeometry.ProjTwistChartBijective
open Stacks.AlgebraicGeometry.ProjTwistComparison (PositiveElem positiveBasicOpen)

universe u

namespace Stacks.AlgebraicGeometry.ProjTwistComparisonIso

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (m : ℕ) (R : Type u) [CommRing R]

/-- The homogeneous coordinates `T₀, …, Tₘ` of `R[T₀, …, Tₘ]`, indexed in the universe of `R`
rather than in `Type 0`: the gluing axiom for sheaves on `Proj` quantifies over index types in
the universe of the space, so the cover of `ℙᵐ_R` by the coordinate charts has to be presented
at that universe. -/
def coord (i : ULift.{u} (Fin (m + 1))) : MvPolynomial (Fin (m + 1)) R :=
  MvPolynomial.X i.down

/-- Each coordinate is homogeneous of degree one. -/
theorem coord_mem (i : ULift.{u} (Fin (m + 1))) : coord m R i ∈ projectiveGrading m R 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R i.down)

/-- **The coordinate standard opens cover `ℙᵐ_R`**, at the `ULift` indexing. -/
theorem iSup_basicOpen_coord_eq_top :
    (⨆ i : ULift.{u} (Fin (m + 1)),
      ProjectiveSpectrum.basicOpen (projectiveGrading m R) (coord m R i)) = ⊤ := by
  refine Eq.trans ?_ (Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top R m)
  exact le_antisymm
    (iSup_le fun i => le_iSup (fun j : Fin (m + 1) =>
      AlgebraicGeometry.Proj.basicOpen (projectiveGrading m R) (MvPolynomial.X j)) i.down)
    (iSup_le fun j => le_iSup (fun i : ULift.{u} (Fin (m + 1)) =>
      ProjectiveSpectrum.basicOpen (projectiveGrading m R) (coord m R i)) (ULift.up j))


/-- **[Stacks, Tag 03GM].** Let `R` be a ring and let `ℱ` be a quasi-coherent sheaf on
`ℙᵐ_R`. For `d ≥ 0` put `M_d = Γ(ℙᵐ_R, ℱ(d))`. Then `M = ⨁_{d ≥ 0} M_d` is a graded
`R[T₀, …, Tₘ]`-module and there is a canonical isomorphism `ℱ = M̃`.

The first conjunct is the graded-module assertion, in three parts: the integer grading
decomposes `M` internally, the grading of `R[T₀, …, Tₘ]` acts on that grading, and the action of
a homogeneous element is the multiplication map of the twists of Equation 03GK. The second and
third are the canonical isomorphism: the comparison `M̃ ⟶ ℱ` is the unique morphism restricting
on each positive-degree standard open `D₊(f)` to `x / f ^ n ↦ x|_{D₊(f)} ⊗ f ^ (-n)`, and it is
invertible.

The source's omitted injectivity and surjectivity arguments are
`Stacks.AlgebraicGeometry.ProjTwistChartBijective.exists_pow_smul_eq_zero_of_numerSection_eq_zero`
and `Stacks.AlgebraicGeometry.ProjTwistChartBijective.exists_numerSection_eq`. -/
@[stacks 03GM "both assertions of the tag in one statement, for a quasi-coherent `ℱ` on `ℙᵐ_R`:
the twisted global sections `M = ⨁_{d ≥ 0} Γ(ℙᵐ_R, ℱ(d))` form a graded `R[T₀, …, Tₘ]`-module --
internally graded, with the grading of the ring acting on the grading of `M`, the action being
the multiplication map of the twists of Equation 03GK -- and the canonical comparison `M̃ ⟶ ℱ`,
the unique morphism restricting on each positive-degree standard open `D₊(f)` to
`x / f ^ n ↦ x|_{D₊(f)} ⊗ f ^ (-n)`, is an isomorphism"]
theorem gradedModule_and_isIso_comparison
    (F : SheafOfModules.{u} (projRingSheaf (projectiveGrading m R)))
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj (projectiveGrading m R)).ringCatSheaf) F) :
    (DirectSum.IsInternal (moduleGrading (projectiveGrading m R) F) ∧
        SetLike.GradedSMul (projectiveGrading m R)
          (moduleGrading (projectiveGrading m R) F) ∧
        ∀ (e k : ℕ) (a : projectiveGrading m R e)
          (s : twistSections (projectiveGrading m R) F k),
          (a : MvPolynomial (Fin (m + 1)) R) •
              DirectSum.of (twistSections (projectiveGrading m R) F) k s =
            DirectSum.of (twistSections (projectiveGrading m R) F) (e + k)
              (gsmul (projectiveGrading m R) F a.2 k (e + k) rfl s)) ∧
      (∃! φ : associatedTwistSectionSheaf (projectiveGrading m R) F ⟶ F,
          ∀ p : PositiveElem (projectiveGrading m R),
            φ.val.app (op (positiveBasicOpen (projectiveGrading m R) p)) =
              positiveChartHom (projectiveGrading m R) F p) ∧
      IsIso (comparison (projectiveGrading m R) F) :=
  ⟨⟨DirectSum.Decomposition.isInternal _, inferInstance,
      fun _ _ a s => smul_of (projectiveGrading m R) F a s⟩,
    existsUnique_comparison (projectiveGrading m R) F,
    isIso_comparison_of_degreeOneCover (projectiveGrading m R) F hqc (coord_mem m R)
      (iSup_basicOpen_coord_eq_top m R)⟩

end Stacks.AlgebraicGeometry.ProjTwistComparisonIso

end
