module

public import StacksFrontier.AlgebraicGeometry.Spaces.CechStructureSheafCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatGlobalFunctions

/-!
# The Čech complex of the structure sheaf of an algebraic space over an affine base

Let `X` be an algebraic space over `Spec A` and `U` an étale chart of `X`. The Čech complex of the
structure sheaf for `U`,
`Γ(U, 𝒪) → Γ(U ×_X U, 𝒪) → Γ(U ×_X U ×_X U, 𝒪) → ⋯`,
is here a `ℤ`-graded complex of `A`-modules in the universe of the schemes. It is the complex
`Stacks.CechTop.cechComplexOverBase` of the small étale ringed site of `X` (whose lift to the
universe of global sections computes `RΓ(X, 𝒪)` when `U` is affine and surjective and `X` has
affine intersections, `AlgebraicGeometry.Space.exists_quasiIso_cechComplexOverBase`), extended by
zero to negative degrees.

This is the complex to which the commutative algebra of degree-zero cohomology and base change,
`CochainComplex.exists_away_nonempty_ker_extendScalars_linearEquiv`, is applied in the proof of
local degree-zero base change for proper flat families (towards Stacks 0E6I, 0E0R, 0E6B).

## Main definitions

* `AlgebraicGeometry.Space.cechStructureComplex`: the complex.

## Main results

* `AlgebraicGeometry.Space.isStrictlyGE_cechStructureComplex`: it vanishes in negative degrees.
* `AlgebraicGeometry.Space.flat_cechStructureComplex_X`: if `X` is flat over `Spec A`, has affine
  intersections, and `U` is affine, its terms are flat `A`-modules.

No declaration of this file carries a `stacks` attribute.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] CategoryTheory.Limits.hasProduct_fin_succ_of_hasBinaryProducts

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
  (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- **The Čech complex of the structure sheaf** of an algebraic space `X` over `Spec A` for an
étale chart `U`: `Γ(U, 𝒪) → Γ(U ×_X U, 𝒪) → ⋯` as `A`-modules, graded by `ℤ`, zero in negative
degrees. -/
abbrev cechStructureComplex (U : SmallEtale B (Spec (.of A)) hA X) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  (Stacks.CechTop.cechComplexOverBase (C := (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C)
    (show (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C from U)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
    (baseRingHom A B hA X hX) (SheafOfModules.unit _)).extend ComplexShape.embeddingUpNat

/-- The Čech complex of the structure sheaf vanishes in negative degrees. -/
instance isStrictlyGE_cechStructureComplex (U : SmallEtale B (Spec (.of A)) hA X) :
    (cechStructureComplex A B hA X hX U).IsStrictlyGE 0 :=
  (CochainComplex.isStrictlyGE_iff _ 0).2 fun p hp =>
    HomologicalComplex.isZero_extend_X _ _ _ fun i => by
      change (i : ℤ) ≠ p
      omega

/-- The degree-`n` term of the Čech complex of the structure sheaf is the module of sections of
the structure sheaf over the `(n+1)`-fold power of the chart. -/
abbrev cechStructureComplexXIso (U : SmallEtale B (Spec (.of A)) hA X) (n : ℕ) :
    (cechStructureComplex A B hA X hX U).X n ≅
      (Stacks.CechTop.sectionsOverBase
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
        (baseRingHom A B hA X hX) (SheafOfModules.unit _)).obj
          (op ((Stacks.CechTop.cechNerve
            (show (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C from U)).obj (op ⦋n⦌))) :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat rfl

/-- **The sections of the structure sheaf over an affine chart flat over `Spec A` are a flat
`A`-module**, for the `A`-module structure of the Čech complex. -/
theorem flat_sectionsOverBase_unit (V : SmallEtale B (Spec (.of A)) hA X)
    (hV : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
      ((SmallEtale.toOver B (Spec (.of A)) hA X).obj V)))
    (hVf : Flat (B.inclusion.map ((SmallEtale.toOver B (Spec (.of A)) hA X).obj V).hom)) :
    Module.Flat A ((Stacks.CechTop.sectionsOverBase
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
        (baseRingHom A B hA X hX) (SheafOfModules.unit _)).obj (op V)) := by
  let := siteObjectAlgebra B A ((SmallEtale.toOver B (Spec (.of A)) hA X).obj V)
  exact flat_siteObjectAlgebra B hV hVf

include hX in
/-- **The terms of the Čech complex of the structure sheaf are flat** when `X` is flat over
`Spec A` with affine intersections and the chart is affine: every power of the chart is then an
affine chart whose structure morphism to `Spec A` is flat. -/
theorem flat_cechStructureComplex_X (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hflat : IsFlat B (Spec (.of A)) hA f) (hsep : HasAffineIntersections B (Spec (.of A)) hA X)
    (U : SmallEtale B (Spec (.of A)) hA X) (hU : IsAffineChart B (Spec (.of A)) hA X U) (p : ℤ) :
    Module.Flat A ((cechStructureComplex A B hA X hX U).X p) := by
  rcases lt_or_ge p 0 with hp | hp
  · have := ModuleCat.subsingleton_of_isZero
      ((cechStructureComplex A B hA X hX U).isZero_of_isStrictlyGE 0 p hp)
    infer_instance
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = p := ⟨p.toNat, by omega⟩
    let V := (Stacks.CechTop.cechNerve
      (show (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C from U)).obj (op ⦋n⦌)
    have := flat_sectionsOverBase_unit A B hA X hX V
      (isAffineChart_cechNerve B (Spec (.of A)) hA X hsep hU n)
      (holdsOnEveryEtaleChart_structure_chart B _ f hflat V.obj.hom V.property)
    exact Module.Flat.of_linearEquiv (cechStructureComplexXIso A B hA X hX U n).toLinearEquiv

end AlgebraicGeometry.Space

end
