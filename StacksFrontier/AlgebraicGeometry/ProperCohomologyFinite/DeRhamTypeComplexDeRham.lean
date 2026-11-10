module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexHypercohomology

/-!
# The relative de Rham complex as a complex with coherent terms

The relative de Rham complex `Ω^•_{X/S}` of a morphism locally of finite type over a locally
Noetherian base is a bounded below complex of `f^{-1}𝒪_S`-modules whose terms are the coherent
`𝒪_X`-modules `Ω^p_{X/S}`, with `f^{-1}𝒪_S`-linear differentials. So the finiteness results of
`StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/DeRhamTypeComplexHypercohomology.lean`
apply to it: for `f` proper over an affine locally Noetherian `S`, the de Rham hypercohomology
modules `H^j(X, Ω^•_{X/S}) = H^j(RΓ(X, Ω^•_{X/S}))` are finite `Γ(S, 𝒪_S)`-modules, and so is the
cohomology of the total Čech complex of `Ω^•_{X/S}` for any cover of `X` by affine opens.

## Main results

* `AlgebraicGeometry.DeRhamTypeComplex.exists_isCoherent_deRhamComplexPlus_X`: the terms of the
  de Rham complex are coherent `𝒪_X`-modules read over `f^{-1}𝒪_S`.
* `AlgebraicGeometry.DeRhamTypeComplex.moduleFinite_hypercohomology_deRhamComplexPlus` and
  `AlgebraicGeometry.DeRhamTypeComplex.moduleFinite_homology_totalCechComplex_deRham`: the
  finiteness of its hypercohomology and of the cohomology of its total Čech complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape
open scoped ZeroObject
open Stacks.DeRhamDirectImage

universe u

namespace AlgebraicGeometry.DeRhamTypeComplex

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The relative de Rham complex `Ω^•_{X/S}`, extended by zero to integer degrees, as a bounded
below complex of `f^{-1}𝒪_S`-modules. -/
def deRhamComplexPlus : CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f)) :=
  ⟨deRhamCochainComplex f, 0, isStrictlyGE_deRhamCochainComplex f⟩

/-- **The terms of the relative de Rham complex are coherent**: in degree `p ≥ 0` the term is
`Ω^p_{X/S}` read over `f^{-1}𝒪_S`, which is coherent for a morphism locally of finite type over
a locally Noetherian base, and in negative degree it is zero. -/
theorem exists_isCoherent_deRhamComplexPlus_X [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (q : ℤ) : ∃ M : X.Modules, M.IsCoherent ∧
      Nonempty ((deRhamComplexPlus f).1.X q ≅ (pushforward (toInverseImageBase f)).obj M) := by
  rcases lt_or_ge q 0 with hq | hq
  · have hz : IsZero ((deRhamComplexPlus f).1.X q) :=
      HomologicalComplex.isZero_extend_X _ embeddingUpNat q (fun i => by
        change ((i : ℕ) : ℤ) ≠ q; omega)
    exact ⟨0, Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero (isZero_zero _),
      ⟨hz.iso ((pushforward (toInverseImageBase f)).map_isZero (isZero_zero _))⟩⟩
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact ⟨Scheme.Hom.relativeDifferentialForms f (n : ℤ),
      Scheme.Hom.isCoherent_relativeDifferentialForms f n,
      ⟨HomologicalComplex.extendXIso _ embeddingUpNat (embeddingUpNat_f n) ≪≫
        eqToIso (Scheme.Hom.deRhamComplex_X f n)⟩⟩

/-- **The de Rham hypercohomology of a proper scheme over an affine Noetherian base is finite**:
for `f : X ⟶ S` proper with `S` affine and locally Noetherian, every
`H^j(X, Ω^•_{X/S}) = H^j(RΓ(X, Ω^•_{X/S}))` is a finite `Γ(S, 𝒪_S)`-module. -/
theorem moduleFinite_hypercohomology_deRhamComplexPlus [IsAffine S] [IsLocallyNoetherian S]
    [IsProper f] (j : ℤ) :
    Module.Finite Γ(S, ⊤) (hypercohomology f (deRhamComplexPlus f) j) :=
  moduleFinite_homology_derivedSections f (deRhamComplexPlus f)
    (exists_isCoherent_deRhamComplexPlus_X f) j

/-- **The total Čech complex of the de Rham complex has finite cohomology**: for `f : X ⟶ S`
proper with `S` affine and locally Noetherian and a cover of `X` by affine opens, the cohomology
of the total complex of the Čech double complex `∏ Ω^q_{X/S}(U_{i_0 … i_p})` is finite over
`Γ(S, 𝒪_S)` in every degree. -/
theorem moduleFinite_homology_totalCechComplex_deRham [IsAffine S] [IsLocallyNoetherian S]
    [IsProper f] {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) (j : ℤ) :
    Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars (inverseImageBaseRingHom f)).obj
      ((totalCechComplex f U hU (deRhamComplexPlus f).1).homology j)) :=
  have : (deRhamComplexPlus f).1.IsStrictlyGE 0 := isStrictlyGE_deRhamCochainComplex f
  moduleFinite_homology_totalCechComplex f U hU hUaff (deRhamComplexPlus f).1 0
    (exists_isCoherent_deRhamComplexPlus_X f) j

end AlgebraicGeometry.DeRhamTypeComplex

end
