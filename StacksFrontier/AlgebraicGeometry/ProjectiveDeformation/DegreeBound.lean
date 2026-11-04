module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.DeformationsOfProjectiveSchemesFunctorial

/-!
# A chosen degree bound for the deformations of a polarized family

[Stacks, Tag 0D4F] (`exists_uniform_degreeBound_functorial`) produces, for a polarized family
`P`, one positive degree `d₀` that works for every admissible deformation of `P` and for every
morphism between two of them. This file fixes such a `d₀` once and for all and names the
conclusions of the tag at it, one statement per conclusion, so that later constructions —
the graded algebra of sections `𝒪_{S'} ⊕ ⨁_{d ≥ d₀} Γ(X', ℒ'^{⊗ d})` of a deformation over an
affine base, and its functoriality — can refer to them without restating the tag.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily.DegreeBoundData`: a degree
  `d₀` together with the conclusions (2)–(5) of [Stacks, Tag 0D4F], its base change clause and
  the invertibility of `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` at `d₀`; the functoriality of `r'` and `θ'` is then
  `canonicalProjHom_comp_projBaseChangeHom` and `canonicalTwistMap_comp_polarization`.
* `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily.degreeBoundData`: one such
  datum, chosen once for the family; `…PolarizedFamily.degreeBound` is its degree.

## Main results

* `…PolarizedFamily.nonempty_degreeBoundData`: [Stacks, Tag 0D4F] produces such a datum.

## Implementation notes

The datum is a structure, chosen with `Classical.choice`, rather than `Classical.choose` applied
to the existential statement of the tag: the predicate of that existential is the whole statement
of the tag, and unifying the degree it chooses with a named constant makes Lean compare two
copies of that predicate, which exhausts the heartbeat budget. Projections out of a structure
need no such comparison. Conclusion (1), the vanishing of higher direct images, is not recorded:
it is stated in a derived category, and the later constructions use it only through the base
change clause and the invertibility of `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)`, which are recorded.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily

open AdmissibleDeformation

/-- **The conclusions of [Stacks, Tag 0D4F] at one degree bound** `d₀` for the polarized family
`P`: conclusions (2)–(5) for every admissible deformation, the base change clause, and the
functoriality of `𝒜'` along every morphism of admissible deformations. -/
structure DegreeBoundData (P : PolarizedFamily.{u}) where
  /-- The degree bound. -/
  d₀ : ℕ
  /-- The degree bound is positive. -/
  pos : 0 < d₀
  /-- Conclusion (2): the pieces `𝒜'_d = (f')_* (ℒ')^{⊗ d}`, `d ≥ d₀`, are finite locally
  free. -/
  isFiniteLocallyFree (D : P.AdmissibleDeformation) (d : ℕ) (hd : d₀ ≤ d) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := D.S'.ringCatSheaf) (D.sectionPiece d)
  /-- The finite presentation clause of conclusion (3). -/
  finitePresentation (D : P.AdmissibleDeformation) (U : D.S'.Opens) (hU : IsAffineOpen U) :
    RingHom.FinitePresentation ((D.truncatedSectionAlgebra d₀ pos).strHom U)
  /-- Conclusion (4): `r' : X' ⟶ Proj_{S'}(𝒜')` is an isomorphism. -/
  isIso_canonicalProjHom (D : P.AdmissibleDeformation) : IsIso (D.canonicalProjHom d₀ pos)
  /-- Conclusion (4): `r'` lies over the base. -/
  canonicalProjHom_comp_toBase (D : P.AdmissibleDeformation) :
    D.canonicalProjHom d₀ pos ≫
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (D.truncatedSectionAlgebra d₀ pos)).toBase = D.f'
  /-- Conclusion (5): `θ' : (r')^* 𝒪(1) ⟶ ℒ'` is an isomorphism. -/
  isIso_canonicalTwistMap (D : P.AdmissibleDeformation) : IsIso (D.canonicalTwistMap d₀ pos)
  /-- The base change clause: for `d ≥ d₀` the formation of `𝒜'_d` commutes with arbitrary base
  change. -/
  isIso_baseChange (D : P.AdmissibleDeformation) (d : ℕ) (hd : d₀ ≤ d) (T Y : Scheme.{u})
    (h : T ⟶ D.S') (fT : Y ⟶ T) (h' : Y ⟶ D.X') (hsq : IsPullback h' fT D.f' h) :
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
      (Stacks.Ample.tensorPowModule D.X' D.L' (d : ℤ)))
  /-- The functoriality of `𝒜'`: `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` is an isomorphism in every degree. -/
  isIso_algebraPullbackHom {D₁ D₂ : P.AdmissibleDeformation} (φ : Hom D₁ D₂) (n : ℤ) :
    IsIso ((algebraPullbackHom φ d₀ pos).app n)

/-- **[Stacks, Tag 0D4F] produces a degree bound datum.** -/
theorem nonempty_degreeBoundData (P : PolarizedFamily.{u}) : Nonempty (DegreeBoundData P) := by
  obtain ⟨d₀, hd₀, h, hφ⟩ := exists_uniform_degreeBound_functorial P
  refine ⟨⟨d₀, hd₀, ?_, ?_, ?_, ?_, ?_, ?_, fun φ => (hφ _ _ φ).fst⟩⟩
  · exact fun D => (h D).2.1
  · exact fun D => (h D).2.2.1.2.2
  · exact fun D => (h D).2.2.2.1.1
  · exact fun D => (h D).2.2.2.1.2
  · exact fun D => (h D).2.2.2.2.1
  · exact fun D => (h D).2.2.2.2.2

/-- **The degree bound datum of [Stacks, Tag 0D4F]**, chosen once for the polarized family. -/
def degreeBoundData (P : PolarizedFamily.{u}) : DegreeBoundData P :=
  Classical.choice (nonempty_degreeBoundData P)

/-- **The degree bound of [Stacks, Tag 0D4F]**, chosen once for the polarized family. -/
abbrev degreeBound (P : PolarizedFamily.{u}) : ℕ := (degreeBoundData P).d₀

/-- The chosen degree bound is positive. -/
theorem degreeBound_pos (P : PolarizedFamily.{u}) : 0 < P.degreeBound :=
  (degreeBoundData P).pos

end Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily

end
