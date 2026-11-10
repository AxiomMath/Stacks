module

public import StacksFrontier.AlgebraicGeometry.ClosedSubschemeProjQuotient.Saturation
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A closed subscheme of `Proj` is the `Proj` of a quotient: a finite chart cover suffices

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a graded ring generated in degree one over `𝒮 0` and let
`i : Z ⟶ Proj 𝒮` be a closed immersion. The identification `Z ≅ Proj (𝒮 / I(Z))` over `Proj 𝒮`
is proved in `StacksFrontier/AlgebraicGeometry/ClosedSubschemeProjQuotient/Saturation.lean` under
the additional hypothesis that `S` be Noetherian. That hypothesis is used in exactly one place:
`AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_mem_idealOfClosedSubscheme` extracts a
*finite* family of degree-one elements whose standard opens cover `Proj 𝒮`, so that one exponent
can be taken to work on every chart at once, and over a Noetherian ring such a family exists
because the irrelevant ideal is finitely generated.

Nothing else about Noetherian rings is used, and the source of Stacks Tag 03GL uses no such
hypothesis: there the finite family is the list of homogeneous coordinates `T₀, …, Tₙ`. This file
therefore restates the chain with the finite family as a hypothesis instead of deducing it, and
instantiates it at a polynomial ring over an **arbitrary** commutative ring.

## Main results

* `Stacks.ProjQuotientFiniteCover.exists_pow_mul_mem_idealOfClosedSubscheme_of_cover`: the
  saturation step with the finite degree-one cover supplied, in place of
  `[IsNoetherianRing S]`.
* `Stacks.ProjQuotientFiniteCover.app_awayMk_eq_zero_iff_of_cover`: the chart comparison, both
  directions, with the finite cover supplied.
* `Stacks.ProjQuotientFiniteCover.saturationIdentification_of_cover`: the identification
  `Z ≅ Proj (𝒮 / I(Z))` over `Proj 𝒮` from a finite degree-one cover, and
  `Stacks.ProjQuotientFiniteCover.ker_eq_ker_ambientHom_of_cover`, the equality of ideal sheaves
  behind it.
* `Stacks.ProjQuotientFiniteCover.projQuotientIso_of_cover` and
  `Stacks.ProjQuotientFiniteCover.projQuotientIso_of_cover_hom_comp_ambientHom`: the isomorphism
  itself and its compatibility with the two morphisms to `Proj 𝒮`;
  `Stacks.ProjQuotientFiniteCover.projQuotientPresentation_of_cover` bundles them with the other
  clauses of `Stacks.ClosedSubschemeProjQuotient.ProjQuotientPresentation`.
* `Stacks.ProjQuotientFiniteCover.projectiveSpace_saturationIdentification`,
  `Stacks.ProjQuotientFiniteCover.projectiveSpace_ker_eq_ker_ambientHom`,
  `Stacks.ProjQuotientFiniteCover.projectiveSpace_projQuotientIso`,
  `Stacks.ProjQuotientFiniteCover.projectiveSpace_projQuotientIso_hom_comp_ambientHom` and
  `Stacks.ProjQuotientFiniteCover.projectiveSpace_projQuotientPresentation`: the polynomial case,
  over an arbitrary commutative coefficient ring. The finite cover is the one by the standard
  opens of the variables, `Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top`.

## Implementation notes

The exponent that works on every chart is `Finset.univ.sup NN` for the per-chart exponents `NN`
of `AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_chartFraction_mem_ker`, which is why
the index type carries `[Fintype ι]`. The family is not required to be nonempty; if it is empty
then the covering hypothesis forces `Proj 𝒮` to be empty and the chartwise criterion
`AlgebraicGeometry.ProjectiveSpectrum.Proj`
`.mem_idealOfClosedSubscheme_of_forall_chartFraction_mem_ker` is vacuous.

Degree indices are kept in the form `k • 1` used by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.chartFraction` and converted with `add_smul` rather
than by a cast, and where an exponent is split `Nat.exists_eq_add_of_le` introduces the difference
as a variable so that `ring` can see `f ^ (a + M) = f ^ a * f ^ M`.

## References

* [Stacks Project, Tag 03GL](https://stacks.math.columbia.edu/tag/03GL)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ClosedSubschemeProjQuotient

universe u w

namespace Stacks.ProjQuotientFiniteCover

/-! ### The saturation step over a finite degree-one cover -/

section GradedRing

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **One exponent serves every chart**, with the finite cover supplied rather than extracted
from a Noetherian hypothesis. If the chart function `b / f ^ n` lies in the kernel of `i` over
`D₊(f)`, and `g` is a finite family of degree-one elements whose standard opens cover `Proj 𝒮`,
then `f ^ N · b` lies in the ideal of equations of `Z` for some `N`.

This is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_mem_idealOfClosedSubscheme` with its
`[IsNoetherianRing S]` hypothesis replaced by the family it is used to produce: the maximum of
the per-chart exponents of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_chartFraction_mem_ker` works on all
charts at once, and padding a chart function by a further power of `f` keeps it in the kernel
because the kernel is an ideal. -/
theorem exists_pow_mul_mem_idealOfClosedSubscheme_of_cover
    {ι : Type*} [Finite ι] (g : ι → S) (hg : ∀ j, g j ∈ 𝒮 1)
    (hcov : ⨆ j, Proj.basicOpen 𝒮 (g j) = ⊤)
    {f : S} (hf : f ∈ 𝒮 1) {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i]
    (n : ℕ) (b : 𝒮 (n • 1))
    (hb : chartFraction 𝒮 hf n b ∈ RingHom.ker (i.app (Proj.basicOpen 𝒮 f)).hom) :
    ∃ N : ℕ, f ^ N * (b : S) ∈ idealOfClosedSubscheme 𝒮 i :=
  exists_pow_mul_mem_idealOfClosedSubscheme 𝒮 Nat.one_pos g hg hcov hf i n b hb

/-- **The chart comparison over a finite degree-one cover.** For `f` of degree one, a degree-zero
fraction `a / f ^ n` with `a` homogeneous of degree `n` is carried to zero by `i` over `D₊(f)`
exactly when some `f ^ j · a` lies in the ideal of equations of `Z`.

The forward implication is `exists_pow_mul_mem_idealOfClosedSubscheme_of_cover`; the backward one
is the vanishing on `Z` of the twisted section of `f ^ j · a`, moved back to the numerator `a` by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.chartFraction_eq_of_cross`. -/
theorem app_awayMk_eq_zero_iff_of_cover
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {ι : Type*} [Finite ι] (g : ι → S) (hg : ∀ j, g j ∈ 𝒮 1)
    (hcov : ⨆ j, Proj.basicOpen 𝒮 (g j) = ⊤)
    {f : S} (hf : f ∈ 𝒮 1) {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i]
    (n : ℕ) (a : S) (ha : a ∈ 𝒮 (n • 1)) :
    (i.app (Proj.basicOpen 𝒮 f)).hom
        ((Proj.awayToSection 𝒮 f).hom (HomogeneousLocalization.Away.mk 𝒮 hf n a ha)) = 0 ↔
      ∃ j : ℕ, f ^ j * a ∈ idealOfClosedSubscheme 𝒮 i := by
  have inst := algebraicGeometry_isInvertible_twistingSheaf 𝒮 hgen
  refine ⟨fun h => exists_pow_mul_mem_idealOfClosedSubscheme_of_cover 𝒮 g hg hcov hf i n
    ⟨a, ha⟩ h, ?_⟩
  rintro ⟨j, hj⟩
  have hmem : f ^ j * a ∈ 𝒮 ((j + n) • 1) := by
    have hp := SetLike.mul_mem_graded (SetLike.pow_mem_graded (A := 𝒮) j hf) ha
    rwa [← add_smul] at hp
  have h1 := chartFraction_mem_ker_app_of_mem_idealOfClosedSubscheme 𝒮 hf Nat.one_pos i
    (j + n) ⟨f ^ j * a, hmem⟩ hj
  rw [chartFraction_eq_of_cross 𝒮 hf (j + n) n ⟨f ^ j * a, hmem⟩ ⟨a, ha⟩
    (by change f ^ j * a * f ^ n = a * f ^ (j + n); ring)] at h1
  exact RingHom.mem_ker.mp h1

end GradedRing

/-! ### The identification -/

section GradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (𝒮 : ℕ → Submodule R S)
  [GradedAlgebra 𝒮]

/-- **A closed subscheme of `Proj 𝒮` is the `Proj` of the quotient by its ideal of equations**,
for a graded ring generated in degree one admitting a *finite* family of degree-one elements whose
standard opens cover `Proj 𝒮`. No Noetherian hypothesis is used.

This is `Stacks.ClosedSubschemeProjQuotient.saturationIdentification` with `[IsNoetherianRing S]`
traded for the finite cover. -/
theorem saturationIdentification_of_cover
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {ι : Type*} [Finite ι] (g : ι → S) (hg : ∀ j, g j ∈ 𝒮 1)
    (hcov : ⨆ j, Proj.basicOpen 𝒮 (g j) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    SaturationIdentification 𝒮 i :=
  Stacks.ProjQuotientChartIdeal.saturationIdentification_of_app_awayMk_eq_ideal 𝒮 i g
    (fun _ => 1) hg (fun _ => Nat.one_pos) hcov
    fun j n a ha => app_awayMk_eq_zero_iff_of_cover 𝒮 hgen g hg hcov (hg j) i n a ha

/-- `Z` and `Proj (𝒮 / I(Z))` cut out the same ideal sheaf of `Proj 𝒮`. -/
theorem ker_eq_ker_ambientHom_of_cover
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {ι : Type*} [Finite ι] (g : ι → S) (hg : ∀ j, g j ∈ 𝒮 1)
    (hcov : ⨆ j, Proj.basicOpen 𝒮 (g j) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    i.ker = (ambientHom 𝒮 i).ker :=
  Stacks.ProjQuotientSaturationKer.ker_eq_of_saturationIdentification 𝒮 i
    (saturationIdentification_of_cover 𝒮 hgen g hg hcov i)

/-- **The isomorphism `Z ≅ Proj (𝒮 / I(Z))`** over a graded ring generated in degree one with a
finite degree-one chart cover. It is the lift of `i` through the closed immersion
`Stacks.ClosedSubschemeProjQuotient.ambientHom`, invertible because the two closed subschemes have
the same ideal sheaf. -/
@[ega "II 2.9.2" "more general"]
def projQuotientIso_of_cover
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {ι : Type*} [Fintype ι] (g : ι → S) (hg : ∀ j, g j ∈ 𝒮 1)
    (hcov : ⨆ j, Proj.basicOpen 𝒮 (g j) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    Z ≅ projQuotient 𝒮 i :=
  haveI : IsClosedImmersion (ambientHom 𝒮 i) := isClosedImmersion_ambientHom 𝒮 i
  haveI : IsIso (IsClosedImmersion.lift (ambientHom 𝒮 i) i
      (ker_eq_ker_ambientHom_of_cover 𝒮 hgen g hg hcov i).symm.le) :=
    IsClosedImmersion.isIso_lift (ambientHom 𝒮 i) i
      (ker_eq_ker_ambientHom_of_cover 𝒮 hgen g hg hcov i).symm
  asIso (IsClosedImmersion.lift (ambientHom 𝒮 i) i
    (ker_eq_ker_ambientHom_of_cover 𝒮 hgen g hg hcov i).symm.le)

/-- **The isomorphism is canonical**: it is compatible with the two morphisms to `Proj 𝒮`, so it
is an equality of closed subschemes of `Proj 𝒮` and not merely an abstract isomorphism. -/
theorem projQuotientIso_of_cover_hom_comp_ambientHom
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {ι : Type*} [Fintype ι] (g : ι → S) (hg : ∀ j, g j ∈ 𝒮 1)
    (hcov : ⨆ j, Proj.basicOpen 𝒮 (g j) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    (projQuotientIso_of_cover 𝒮 hgen g hg hcov i).hom ≫ ambientHom 𝒮 i = i :=
  have : IsClosedImmersion (ambientHom 𝒮 i) := isClosedImmersion_ambientHom 𝒮 i
  IsClosedImmersion.lift_fac (ambientHom 𝒮 i) i
    (ker_eq_ker_ambientHom_of_cover 𝒮 hgen g hg hcov i).symm.le

/-- **Every clause of the presentation of a closed subscheme of `Proj 𝒮` as a `Proj`**, over a
graded ring generated in degree one with a finite degree-one chart cover. -/
def projQuotientPresentation_of_cover
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {ι : Type*} [Fintype ι] (g : ι → S) (hg : ∀ j, g j ∈ 𝒮 1)
    (hcov : ⨆ j, Proj.basicOpen 𝒮 (g j) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    ProjQuotientPresentation 𝒮 i where
  quotient_epi := surjective_quotientMk 𝒮 i
  quotient_kernel := quotientMk_coe_eq_zero_iff 𝒮 i
  isClosedImmersion_ambient := isClosedImmersion_ambientHom 𝒮 i
  iso := projQuotientIso_of_cover 𝒮 hgen g hg hcov i
  iso_over_ambient := projQuotientIso_of_cover_hom_comp_ambientHom 𝒮 hgen g hg hcov i

end GradedAlgebra

/-! ### Projective space over an arbitrary ring -/

section ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (e : ℕ)

/-- **A closed subscheme of `Proj R[T₀, …, T_{e-1}]` is `Proj` of the quotient by its homogeneous
ideal of equations, over an arbitrary commutative coefficient ring.** The polynomial grading is
generated in degree one, and the standard opens of the finitely many variables cover `Proj`, so
`saturationIdentification_of_cover` applies with no Noetherian hypothesis. -/
theorem projectiveSpace_saturationIdentification {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin e) R)) [IsClosedImmersion i] :
    SaturationIdentification (MvPolynomial.homogeneousSubmodule (Fin e) R) i :=
  saturationIdentification_of_cover _
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin e) R) MvPolynomial.X
    (fun j => MvPolynomial.isHomogeneous_X R j)
    (Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top R (Fin e)) i

/-- `Z` and `Proj (R[T]/I(Z))` cut out the same ideal sheaf of `Proj R[T]`, over an arbitrary
commutative coefficient ring. -/
theorem projectiveSpace_ker_eq_ker_ambientHom {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin e) R)) [IsClosedImmersion i] :
    i.ker = (ambientHom (MvPolynomial.homogeneousSubmodule (Fin e) R) i).ker :=
  ker_eq_ker_ambientHom_of_cover _
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin e) R) MvPolynomial.X
    (fun j => MvPolynomial.isHomogeneous_X R j)
    (Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top R (Fin e)) i

/-- **The isomorphism `Z ≅ Proj (R[T₀, …, T_{e-1}]/I(Z))`**, over an arbitrary commutative
coefficient ring. -/
def projectiveSpace_projQuotientIso {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin e) R)) [IsClosedImmersion i] :
    Z ≅ projQuotient (MvPolynomial.homogeneousSubmodule (Fin e) R) i :=
  projQuotientIso_of_cover _
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin e) R) MvPolynomial.X
    (fun j => MvPolynomial.isHomogeneous_X R j)
    (Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top R (Fin e)) i

/-- The isomorphism of `projectiveSpace_projQuotientIso` is compatible with the two morphisms to
`Proj R[T₀, …, T_{e-1}]`. -/
theorem projectiveSpace_projQuotientIso_hom_comp_ambientHom {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin e) R)) [IsClosedImmersion i] :
    (projectiveSpace_projQuotientIso R e i).hom ≫
        ambientHom (MvPolynomial.homogeneousSubmodule (Fin e) R) i = i :=
  projQuotientIso_of_cover_hom_comp_ambientHom _
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin e) R) MvPolynomial.X
    (fun j => MvPolynomial.isHomogeneous_X R j)
    (Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top R (Fin e)) i

/-- **Every clause of the presentation of a closed subscheme of projective space as a `Proj`**,
over an arbitrary commutative coefficient ring. -/
def projectiveSpace_projQuotientPresentation {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin e) R)) [IsClosedImmersion i] :
    ProjQuotientPresentation (MvPolynomial.homogeneousSubmodule (Fin e) R) i :=
  projQuotientPresentation_of_cover _
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin e) R) MvPolynomial.X
    (fun j => MvPolynomial.isHomogeneous_X R j)
    (Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top R (Fin e)) i

end ProjectiveSpace

end Stacks.ProjQuotientFiniteCover

end
