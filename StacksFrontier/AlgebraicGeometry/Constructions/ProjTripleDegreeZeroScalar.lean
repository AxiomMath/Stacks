module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleUnitSection
public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic

/-!
# The structure morphism of a triple, and the scalars its degree-zero part supplies

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `Y` a scheme, `L` an invertible `𝒪_Y`-module and
`ψ : A^{(d)} ⟶ Γ_*(Y, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`. Over an affine base `S`, the
degree-zero part of `ψ` determines a morphism `Y ⟶ S`, from the ring map
`Γ(S, 𝒪_S) → A_0 → Γ(Y, 𝒪_Y)` through [Stacks, Tag 01I1], and the degreewise maps of `ψ` are
linear over `Γ(S, 𝒪_S)` acting through that morphism.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTripleDegreeZeroScalar.structureMorphism`: the morphism `Y ⟶ S` a
  triple determines over an affine base, for a given ring map `c : Γ(S, 𝒪_S) ⟶ A_0`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTripleDegreeZeroScalar.toFun_mul_degreeZero`: multiplication by a
  degree-zero element acts on the degreewise maps of `ψ` as a scalar, namely the image of that
  element under the degree-zero ring map.
* `Stacks.AlgebraicGeometry.ProjTripleDegreeZeroScalar.structureMorphism_appTop`: the recovered
  morphism induces `c` followed by the degree-zero ring map on global sections.
* `Stacks.AlgebraicGeometry.ProjTripleDegreeZeroScalar.toFun_mul_appTop`: the degreewise maps of
  `ψ` are `Γ(S, 𝒪_S)`-linear through `f^♯`, `f` the recovered morphism: multiplying a homogeneous
  element by the degree-zero element `c(r)` multiplies its image by `f^♯(r)`.
* `Stacks.AlgebraicGeometry.ProjTripleDegreeZeroScalar.toProj_comp_toSpecZero_structureMorphism`:
  the morphism classified by the triple, composed with `Proj A ⟶ Spec A_0 ⟶ S`, is the recovered
  morphism.

## Implementation notes

`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.map_mul` is used in the bidegree
`(n, 0)` rather than `(0, n)`: `(n + 0) * d` reduces to `n * d`, whereas `(0 + n) * d` does not,
so no transport along an equality of degrees is needed.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (IsCompatible psiSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjSectionsUnique (Pair)
open Stacks.AlgebraicGeometry.ProjTripleStructureMorphism
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTripleDegreeZeroScalar

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L] (ψ : VeroneseSections 𝒜 d L)
  (hone : ∀ a : 𝒜 (0 * d), (a : A) = 1 → ψ.toFun 0 a = unitGlobal L)

/-! ### Degree-zero elements act as scalars -/

/-- **Multiplication by a degree-zero element acts on the degreewise maps of `ψ` as a scalar.**
If a homogeneous element `az` of degree `nd` is the product of a homogeneous element `a` of the
same degree with a degree-zero element `z`, then `ψ(az) = degreeZeroHom(z) · ψ(a)` as global
sections of `L ^⊗ n`. -/
theorem toFun_mul_degreeZero (n : ℕ) (a : 𝒜 (n * d)) (z : 𝒜 0) (az : 𝒜 (n * d))
    (h : (az : A) = (a : A) * (z : A)) :
    ψ.toFun n az = degreeZeroHom 𝒜 ψ hone z • ψ.toFun n a := by
  have hmul := ψ.map_mul n 0 a (zeroVeronese 𝒜 d z) az h
  have h2 : resTop (natTensorPow L 0) (ψ.toFun 0 (zeroVeronese 𝒜 d z)) ⊤
      = degreeZeroHom 𝒜 ψ hone z • resTop (natTensorPow L 0) (unitGlobal L) ⊤ := by
    rw [resTop_eq_self]
    exact toFun_zero_eq_smul 𝒜 ψ hone z
  have h3 := resTop_mulSections_smul_right L (ψ.toFun n a) h2
  rw [Stacks.AlgebraicGeometry.ProjTripleUnitSection.mulSections_unitGlobal_right,
    resTop_eq_self, resTop_eq_self] at h3
  exact hmul.trans h3

/-- **`toFun_mul_degreeZero` for a `ψ` satisfying the generation condition of a triple**, with no
unit hypothesis. -/
theorem toFun_mul_degreeZero_of_generated
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    (n : ℕ) (a : 𝒜 (n * d)) (z : 𝒜 0) (az : 𝒜 (n * d))
    (h : (az : A) = (a : A) * (z : A)) :
    ψ.toFun n az
      = degreeZeroHom 𝒜 ψ
          (Stacks.AlgebraicGeometry.ProjTripleUnitSection.toFun_zero_eq_unitGlobal 𝒜 ψ hgen) z
        • ψ.toFun n a :=
  toFun_mul_degreeZero 𝒜 ψ
    (Stacks.AlgebraicGeometry.ProjTripleUnitSection.toFun_zero_eq_unitGlobal 𝒜 ψ hgen) n a z az h

/-! ### The structure morphism over an affine base -/

section Affine

variable {S : Scheme.{u}} [IsAffine S] (c : Γ(S, ⊤) ⟶ CommRingCat.of (𝒜 0))

/-- **The morphism `Y ⟶ S` a triple determines over an affine base.** For a ring map
`c : Γ(S, 𝒪_S) ⟶ A_0` — in [Stacks, Tag 01NU], where `S = Spec(R)` and `A = Γ(S, 𝒜)`, the
structure map `R → A_0` of the graded `R`-algebra `A` — this is the morphism of schemes that the
composite `Γ(S, 𝒪_S) → A_0 → Γ(Y, 𝒪_Y)` determines through the affine adjunction of [Stacks, Tag
01I1]. Unfolded, it is `Y ⟶ Spec Γ(Y, 𝒪_Y) ⟶ Spec Γ(S, 𝒪_S) ≅ S`. -/
def structureMorphism : Y ⟶ S :=
  (Stacks.RelativeSpec.affineHomEquiv S Y).symm
    (c ≫ CommRingCat.ofHom (degreeZeroHom 𝒜 ψ hone))

/-- **The recovered morphism induces `c` followed by the degree-zero ring map of the triple on
global sections**, which by [Stacks, Tag 01I1] characterises it. -/
@[simp]
theorem structureMorphism_appTop :
    (structureMorphism 𝒜 ψ hone c).appTop = c ≫ CommRingCat.ofHom (degreeZeroHom 𝒜 ψ hone) :=
  Stacks.RelativeSpec.affineHomEquiv_symm_appTop _

/-- The effect of the recovered morphism on a function on `S`. -/
theorem structureMorphism_appTop_apply (r : Γ(S, ⊤)) :
    (structureMorphism 𝒜 ψ hone c).appTop r = degreeZeroHom 𝒜 ψ hone (c r) := by
  rw [structureMorphism_appTop]
  rfl

/-- **The degreewise maps of `ψ` are `Γ(S, 𝒪_S)`-linear through `f^♯`**, `f` the recovered
morphism: multiplying a homogeneous element of degree `nd` by the degree-zero element `c(r)`
multiplies its image under `ψ` by the function `f^♯(r)`. -/
theorem toFun_mul_appTop (n : ℕ) (r : Γ(S, ⊤)) (a : 𝒜 (n * d)) (az : 𝒜 (n * d))
    (h : (az : A) = (a : A) * ((c r : 𝒜 0) : A)) :
    ψ.toFun n az = (structureMorphism 𝒜 ψ hone c).appTop r • ψ.toFun n a := by
  rw [structureMorphism_appTop_apply]
  exact toFun_mul_degreeZero 𝒜 ψ hone n a (c r) az h

/-- **The morphism classified by the triple, composed with `Proj A ⟶ Spec A_0 ⟶ S`, is the
recovered morphism.** -/
theorem toProj_comp_toSpecZero_structureMorphism (hd : 0 < d)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    {p : Pair 𝒜 L d} (hp : IsCompatible 𝒜 ψ p) :
    toProj 𝒜 p.1 ≫ AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫ Spec.map c ≫ S.isoSpec.inv
      = structureMorphism 𝒜 ψ hone c :=
  comp_eq_of_appTop_eq 𝒜 ψ hone hd hgen hp c (structureMorphism 𝒜 ψ hone c)
    (structureMorphism_appTop 𝒜 ψ hone c)

end Affine

end Stacks.AlgebraicGeometry.ProjTripleDegreeZeroScalar

end
