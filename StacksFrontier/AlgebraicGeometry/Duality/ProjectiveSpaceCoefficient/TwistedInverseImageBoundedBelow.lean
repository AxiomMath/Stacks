module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EulerCharVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistedInverseImageProjToSpec
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardBounds

/-!
# The twisted inverse image of `ℙⁿ_R ⟶ Spec R` lowers the lower bound by at most `n`

Let `R` be a commutative ring, `n ≥ 0`, `p : ℙⁿ_R ⟶ Spec R` the structure morphism and
`a = p^×` the right adjoint of `Rp_* : D_QCoh(𝒪_{ℙⁿ_R}) ⥤ D_QCoh(𝒪_{Spec R})`. This file proves
that `a` carries `D^{≥ b}_QCoh` into `D^{≥ b - n}_QCoh`.

The argument is the one of [Stacks, Tag 0A9I] with the uniform bound of [Stacks, Tag 08D5]
part (2) made explicit: for `p` the bound is `n`. Indeed, over an affine open `V ⊆ Spec R` the
inverse image `p⁻¹V` is covered by the `n + 1` affine opens `D₊(Tᵢ) ∩ p⁻¹V`, and `ℙⁿ_R` has affine
diagonal, so quasi-coherent cohomology over `p⁻¹V` vanishes in degrees `≥ n + 1`
([Stacks, Tag 01XD]). Part (3) of [Stacks, Tag 08D4] then bounds `RΓ(p⁻¹V, E)` by `b + n` for
`E ∈ D^{≤ b}_QCoh`, and `H^i(Rp_*E)` is the sheafification of `V ↦ H^i(p⁻¹V, E)`
([Stacks, Tag 0D66]), so `Rp_*E ∈ D^{≤ b + n}`. Adjunction does the rest
(`Stacks.Duality.isGE_rightAdjoint_obj`).

## Main results

* `Stacks.Duality.ProjCoeff.isZero_Hgroup_preimage_projToSpecCoeff` — quasi-coherent cohomology
  over the inverse image of an affine open of `Spec R` vanishes in degrees `> n`.
* `Stacks.Duality.ProjCoeff.isLE_derivedPushforward_of_modulePushforward` — an explicit bound for
  the termwise direct image of K-injective resolutions is a bound for `Rf_*` at any chosen model
  of the derived categories.
* `Stacks.Duality.ProjCoeff.isLE_derivedPushforward_projToSpecCoeff` — `Rp_*` has cohomological
  amplitude `≤ n` on complexes with quasi-coherent cohomology, at any chosen model.
* `Stacks.Duality.ProjCoeff.isGE_twistedInverseImageProjToSpec` — **`a` carries `D^{≥ b}_QCoh`
  into `D^{≥ b - n}_QCoh`.**

## Implementation notes

The explicit bound is first obtained at `HasDerivedCategory.standard`, where the hypercohomology
machinery of [Stacks, Tag 08D4] and [Stacks, Tag 0D66] is stated, then expressed with no derived
category at all (the cohomology of `p_*I` for a K-injective resolution `K ⟶ I`), and finally read
back at an arbitrary model through `Stacks.Duality.derivedPushforwardObjIso`. This is the route of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/UniformBoundAnyModel.lean`, which does
the same for a non-explicit bound. The twisted inverse image exists only at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is what the final statement uses.

## References

* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.ProjectiveCohomology (polyGrading)

universe w u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.ProjCoeff

/-! ### Explicit bounds transfer to any model -/

section AnyModel

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- **An explicit bound for the direct image of K-injective resolutions bounds `Rf_*` at any
model.** Suppose that for every complex `K` of `𝒪_X`-modules with quasi-coherent cohomology
vanishing above degree `b`, and every K-injective resolution `K ⟶ I`, the complex `f_*I` has
vanishing cohomology above degree `b + N`. Then, at any chosen model of the derived categories,
`Rf_*E` lives in degrees `≤ b + N` whenever `E` has quasi-coherent cohomology in degrees `≤ b`.

`Stacks.Duality.derivedPushforwardObjIso` identifies `Rf_*E` with the object represented by
`f_*I`. -/
theorem isLE_derivedPushforward_of_modulePushforward (N : ℤ)
    (hN : ∀ (K I : CochainComplex X.Modules ℤ),
      (∀ n : ℤ, (K.homology n).IsQuasicoherent) → ∀ b : ℤ,
      (∀ n : ℤ, b < n → IsZero (K.homology n)) →
      ∀ s : K ⟶ I, I.IsKInjective → QuasiIso s → ∀ m : ℤ, b + N < m →
        IsZero ((((Scheme.Modules.pushforward f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I).homology m))
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) : ((derivedPushforward.{w} f).obj E).IsLE (b + N) := by
  rw [DerivedCategory.isLE_iff]
  intro m hm
  set K := DerivedCategory.Q.objPreimage E
  let eQ : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let eE : DerivedCategory.Qh.obj ((HomotopyCategory.quotient X.Modules
      (ComplexShape.up ℤ)).obj K) ≅ E :=
    (DerivedCategory.quotientCompQhIso X.Modules).app K ≪≫ eQ
  have eK : ∀ n : ℤ, (DerivedCategory.homologyFunctor X.Modules n).obj E ≅ K.homology n :=
    fun n => ((DerivedCategory.homologyFunctor X.Modules n).mapIso eQ).symm ≪≫
      (DerivedCategory.homologyFunctorFactors X.Modules n).app K
  have hKcoh : ∀ n : ℤ, (K.homology n).IsQuasicoherent := fun n =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (eK n) (hcoh n)
  have hKle : ∀ n : ℤ, b < n → IsZero (K.homology n) := fun n hn =>
    (DerivedCategory.isZero_of_isLE E b n hn).of_iso (eK n).symm
  obtain ⟨I, s, hI, hs⟩ := AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective X K
  exact (hN K I hKcoh b hKle s hI hs m hm).of_iso
    ((((DerivedCategory.homologyFunctorFactors Y.Modules m).app _).symm ≪≫
      (DerivedCategory.homologyFunctor Y.Modules m).mapIso
        ((Stacks.Duality.derivedPushforwardObjIso.{w} f s hI hs).symm ≪≫
          (derivedPushforward.{w} f).mapIso eE)).symm)

end AnyModel

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### Cohomology over the inverse image of an affine open -/

/-- **Quasi-coherent cohomology of `ℙⁿ_R` over the inverse image of an affine open of `Spec R`
vanishes in degrees `> n`.** The opens `D₊(Tᵢ) ∩ p⁻¹V`, `i = 0, …, n`, are affine and cover
`p⁻¹V`, and `ℙⁿ_R` has affine diagonal, so the Čech computation of [Stacks, Tag 01XD] applies
with `n + 1` opens. -/
theorem isZero_Hgroup_preimage_projToSpecCoeff (V : (Spec (CommRingCat.of R)).Opens)
    (hV : IsAffineOpen V) (F : (AlgebraicGeometry.Proj (polyGrading R n)).Modules)
    [F.IsQuasicoherent] (q : ℕ) (hq : n + 1 ≤ q) :
    IsZero (Hgroup (AlgebraicGeometry.Proj (polyGrading R n)).ringCatSheaf
      (projToSpecCoeff R n ⁻¹ᵁ V) q F) := by
  have hdiag : IsAffineHom (pullback.diagonal
      (terminal.from (AlgebraicGeometry.Proj (polyGrading R n)))) := inferInstance
  refine @Stacks.Cohomology.FiniteCover.isZero_Hgroup_of_finite_affine_cover
    (AlgebraicGeometry.Proj (polyGrading R n)) hdiag F inferInstance (n + 1)
    (fun i : Fin (n + 1) =>
      Proj.basicOpen (polyGrading R n) (MvPolynomial.X i) ⊓ projToSpecCoeff R n ⁻¹ᵁ V)
    (fun i => IsAffineOpen.inf_preimage _
      (Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X R i) one_pos)
      (isAffineOpen_top (Spec (CommRingCat.of R))) hV (by simp) le_top)
    _ ?_ q hq
  rw [← iSup_inf_eq, Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top R n, top_inf_eq]

/-! ### The amplitude of `Rp_*` -/

section Standard

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.UnboundedHigherDirectImage.isGrothendieckAbelian_moduleSheaves

/-- **`Rp_*` has cohomological amplitude `≤ n`, at `HasDerivedCategory.standard`.** For `E` in
`D(𝒪_{ℙⁿ_R})` with quasi-coherent cohomology living in degrees `≤ b`, `Rp_*E` lives in degrees
`≤ b + n`. The cohomology sheaves of `Rp_*E` are sheafifications of `V ↦ H^i(p⁻¹V, E)`
([Stacks, Tag 0D66]), and over affine `V` those vanish above `b + n` by
[Stacks, Tag 08D4] part (3) and `isZero_Hgroup_preimage_projToSpecCoeff`. -/
theorem isLE_derivedPushforward_projToSpecCoeff_standard
    (E : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (AlgebraicGeometry.Proj (polyGrading R n)).toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing (AlgebraicGeometry.Proj (polyGrading R n)).toRingedSpace)) i).obj
        E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) :
    ((RingedSpace.derivedPushforward (projToSpecCoeff R n).toLRSHom.toShHom).obj E).IsLE
      (b + n) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine Stacks.Cohomology.UnboundedHigherDirectImage.isZero_homologyDerivedPushforward_of_isBasis
    (projToSpecCoeff R n).toLRSHom.toShHom (Spec (CommRingCat.of R)).isBasis_affineOpens E i
    fun V hV ↦ ?_
  have := isLE_derivedPreimageSections_obj_of_isZero_hgroup (projToSpecCoeff R n) V (n + 1)
    (fun F _ q hq ↦ isZero_Hgroup_preimage_projToSpecCoeff R n V hV F q hq) E hcoh b hE
  refine DerivedCategory.isZero_of_isLE _ (b + ((n + 1 : ℕ) : ℤ) - 1) i ?_
  push_cast
  omega

/-- **The amplitude bound for `Rp_*` with no derived category in the statement.** For a complex
`K` of `𝒪_{ℙⁿ_R}`-modules with quasi-coherent cohomology vanishing above degree `b` and a
K-injective resolution `K ⟶ I`, the complex `p_*I` has vanishing cohomology above degree
`b + n`. -/
theorem isZero_homology_modulePushforward_projToSpecCoeff
    (K I : CochainComplex (AlgebraicGeometry.Proj (polyGrading R n)).Modules ℤ)
    (hqc : ∀ m : ℤ, (K.homology m).IsQuasicoherent) (b : ℤ)
    (hle : ∀ m : ℤ, b < m → IsZero (K.homology m))
    (s : K ⟶ I) (hI : I.IsKInjective) (hs : QuasiIso s) (m : ℤ) (hm : b + n < m) :
    IsZero ((((Scheme.Modules.pushforward (projToSpecCoeff R n)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology m) := by
  let X := AlgebraicGeometry.Proj (polyGrading R n)
  have hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient X.Modules
        (ComplexShape.up ℤ)).obj K))).IsQuasicoherent := fun j =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Stacks.Duality.homologyQhObjIso K j).symm (hqc j)
  have hEle : (DerivedCategory.Qh.obj ((HomotopyCategory.quotient X.Modules
      (ComplexShape.up ℤ)).obj K)).IsLE b := by
    rw [DerivedCategory.isLE_iff]
    exact fun j hj ↦ (hle j hj).of_iso (Stacks.Duality.homologyQhObjIso K j)
  have : ((Stacks.Duality.derivedPushforward (projToSpecCoeff R n)).obj (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K))).IsLE (b + n) :=
    isLE_derivedPushforward_projToSpecCoeff_standard R n _ hcoh b hEle
  have hbase : IsZero ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of R)).Modules m).obj
      ((Stacks.Duality.derivedPushforward (projToSpecCoeff R n)).obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K)))) :=
    DerivedCategory.isZero_of_isLE _ (b + n) m hm
  exact hbase.of_iso (((DerivedCategory.homologyFunctor _ m).mapIso
      (Stacks.Duality.derivedPushforwardObjIso (projToSpecCoeff R n) s hI hs) ≪≫
    (DerivedCategory.homologyFunctorFactors _ m).app _).symm)

end Standard

/-- **`Rp_*` has cohomological amplitude `≤ n` on complexes with quasi-coherent cohomology, at
any chosen model of the derived categories.** For `E` in `D(𝒪_{ℙⁿ_R})` with quasi-coherent
cohomology living in degrees `≤ b`, `Rp_*E` lives in degrees `≤ b + n`. -/
theorem isLE_derivedPushforward_projToSpecCoeff
    [HasDerivedCategory.{w} (AlgebraicGeometry.Proj (polyGrading R n)).Modules]
    [HasDerivedCategory.{w} (Spec (CommRingCat.of R)).Modules]
    (E : DerivedCategory (AlgebraicGeometry.Proj (polyGrading R n)).Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.Proj (polyGrading R n)).Modules j).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) :
    ((derivedPushforward.{w} (projToSpecCoeff R n)).obj E).IsLE (b + n) :=
  isLE_derivedPushforward_of_modulePushforward (projToSpecCoeff R n) n
    (isZero_homology_modulePushforward_projToSpecCoeff R n) E hcoh b hE

/-! ### The twisted inverse image -/

/-- **The twisted inverse image of `p : ℙⁿ_R ⟶ Spec R` carries `D^{≥ b}_QCoh` into
`D^{≥ b - n}_QCoh`.** If `K ∈ D_QCoh(𝒪_{Spec R})` lives in degrees `≥ b`, then `p^×K` lives in
degrees `≥ b - n`.

For `F ∈ D^{≤ b - n - 1}_QCoh(𝒪_{ℙⁿ_R})` one has `Hom(F, p^×K) = Hom(Rp_*F, K) = 0`, because
`Rp_*F` lives in degrees `≤ b - 1` (`isLE_derivedPushforward_projToSpecCoeff`); applied to the
truncation `τ^{≤ b - n - 1}(p^×K)`, which again has quasi-coherent cohomology, this is the argument
of [Stacks, Tag 0A9I], `Stacks.Duality.isGE_rightAdjoint_obj`. -/
theorem isGE_twistedInverseImageProjToSpec
    (K : Stacks.Duality.quasiCoherentDerivedCategory (Spec (.of R))) (b : ℤ)
    (hK : K.obj.IsGE b) :
    ((Stacks.ProjectiveSpace.Cohomology.twistedInverseImageProjToSpec R n).obj K).obj.IsGE
      (b - n) :=
  Stacks.Duality.isGE_rightAdjoint_obj _ _
    (Stacks.ProjectiveSpace.Cohomology.adjunction_quasiCoherentDerivedPushforward_projToSpecCoeff
      R n) n (isLE_derivedPushforward_projToSpecCoeff R n) K b hK

end Stacks.Duality.ProjCoeff

end
