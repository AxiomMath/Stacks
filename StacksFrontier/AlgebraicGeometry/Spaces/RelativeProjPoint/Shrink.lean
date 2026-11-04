module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSmallPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# Shrinking the module universe of Situation 0849

In Situation 0849 (`AlgebraicGeometry.Space.RelativeProjSituation`) the homogeneous pieces of the
graded algebra `𝒜` have their sections in an arbitrary universe `m`, but those sections are bounded
by the cutoff of the big fppf site, a cardinal of the universe `u`. So `𝒜` can be re-presented as a
graded algebra with sections in `u`, by `SheafOfModules.GradedAlgebra.smallPresentation`; the
re-presentation is identified with `𝒜` degreewise and sectionwise, compatibly with restriction,
multiplication and unit. It is again commutative, concentrated in nonnegative degrees,
quasi-coherent and bounded by the cutoff, so it gives a situation at the universes `u, u` with the
same site, base and algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebra`: the re-presented graded algebra.
* `AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebraEquiv`: its comparison with `𝒜`.
* `AlgebraicGeometry.Space.RelativeProjSituation.shrink`: the situation with the re-presented
  algebra.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.isQuasicoherent_smallAlgebra`: the pieces of the
  re-presented algebra are quasi-coherent. Quasi-coherence is insensitive to the universe of the
  sections: `SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'` and
  `SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'`.

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 000H](https://stacks.math.columbia.edu/tag/000H)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- The homogeneous sections of the algebra are `u`-small: they are bounded by the cutoff of
the site, a cardinal of the universe `u`. -/
instance small_sections (n : ℤ) (U : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ) :
    Small.{u} ((s.algebra.piece n).val.obj U) :=
  (s.sections_hasCardinalLT n U).small

/-- **The graded algebra of the situation, re-presented with its sections in the universe `u`**:
the small presentation `SheafOfModules.GradedAlgebra.smallPresentation`, available because the
homogeneous sections are bounded by the cutoff of the site. -/
def smallAlgebra : SheafOfModules.GradedAlgebra.{u, u}
    (structureRingSheaf s.site s.base s.containsBase s.space) :=
  SheafOfModules.GradedAlgebra.smallPresentation.{u, m, u} s.algebra

/-- **The comparison of the re-presented algebra with the original one**: in each degree and
over each étale object an `𝒪(U)`-linear bijection of sections, natural in `U`. It carries the
multiplication and the unit of `smallAlgebra` to those of the original algebra
(`smallAlgebraEquiv_mul_app`, `smallAlgebraEquiv_one_eval`). -/
def smallAlgebraEquiv : SheafOfModules.GradedAlgebra.PieceEquiv s.algebra s.smallAlgebra.piece :=
  SheafOfModules.GradedAlgebra.smallPresentationEquiv s.algebra

/-- The comparison carries the multiplication of `smallAlgebra` to that of the algebra. -/
theorem smallAlgebraEquiv_mul_app (i j : ℤ)
    (U : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (x : (s.smallAlgebra.piece i).val.obj U) (y : (s.smallAlgebra.piece j).val.obj U) :
    s.smallAlgebraEquiv.equiv (i + j) U ((s.smallAlgebra.mul i j).app U x y) =
      (s.algebra.mul i j).app U (s.smallAlgebraEquiv.equiv i U x)
        (s.smallAlgebraEquiv.equiv j U y) :=
  SheafOfModules.GradedAlgebra.smallPresentation_equiv_mul_app s.algebra i j U x y

/-- The comparison carries the unit of `smallAlgebra` to that of the algebra. -/
theorem smallAlgebraEquiv_one_eval (U : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ) :
    s.smallAlgebraEquiv.equiv 0 U (s.smallAlgebra.one.eval U) = s.algebra.one.eval U :=
  SheafOfModules.GradedAlgebra.smallPresentation_equiv_one_eval s.algebra U


/-- The homogeneous pieces of the re-presented algebra are quasi-coherent: after raising both
to a common universe they are isomorphic to those of the algebra, and quasi-coherence is unchanged
by raising the universe of the sections, in either direction. -/
theorem isQuasicoherent_smallAlgebra (n : ℤ) : (s.smallAlgebra.piece n).IsQuasicoherentOnSite := by
  have h₁ : (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u}
      (s.algebra.piece n)).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_uliftForPresentation' (s.isQuasicoherent n)
  have h₂ : (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, m}
      (s.smallAlgebra.piece n)).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (SheafOfModules.GradedAlgebra.smallPresentationPieceIso s.algebra n).symm h₁
  exact SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation' h₂

/-- The homogeneous pieces of negative degree of the re-presented algebra vanish. -/
theorem isZero_smallAlgebra_piece (n : ℤ) (hn : n < 0) : IsZero (s.smallAlgebra.piece n) := by
  have h₁ : IsZero ((Stacks.SheafOfModules.moduleULift.{u, m} _).obj (s.algebra.piece n)) :=
    Functor.map_isZero _ (s.negative_isZero n hn)
  have h₂ : IsZero ((Stacks.SheafOfModules.moduleULift.{m, u} _).obj (s.smallAlgebra.piece n)) :=
    h₁.of_iso (SheafOfModules.GradedAlgebra.smallPresentationPieceIso s.algebra n)
  rw [IsZero.iff_id_eq_zero] at h₂ ⊢
  apply (Stacks.SheafOfModules.moduleULiftFullyFaithful.{m, u} _).map_injective
  simpa using h₂

/-- **Situation 0849 with the module universe shrunk to `u`.** The same site, base and algebraic
space, with the graded algebra replaced by its re-presentation `smallAlgebra`; all the conditions
of the situation carry over along the comparison `smallAlgebraEquiv`.

This is a reducible alias: `s.shrink.site`, `s.shrink.base`, `s.shrink.containsBase` and
`s.shrink.space` are `s.site`, `s.base`, `s.containsBase` and `s.space` at reducible
transparency, so the two spellings of the site, the base and the space are never compared by
unfolding anything but this alias. The one new object is the algebra `smallAlgebra`, with its
characterising API (`smallAlgebraEquiv`, `smallAlgebraEquiv_mul_app`, `smallAlgebraEquiv_one_eval`,
`isQuasicoherent_smallAlgebra`, `isZero_smallAlgebra_piece`). -/
abbrev shrink : RelativeProjSituation.{u, u} where
  site := s.site
  base := s.base
  containsBase := s.containsBase
  space := s.space
  algebra := s.smallAlgebra
  mul_comm i j U _ _ :=
    (SheafOfModules.GradedAlgebra.smallPresentationEquiv s.algebra).heq_symm U (add_comm i j)
      (s.mul_comm i j U _ _)
  negative_isZero := s.isZero_smallAlgebra_piece
  isQuasicoherent := s.isQuasicoherent_smallAlgebra
  sections_hasCardinalLT n U :=
    (hasCardinalLT_iff_of_equiv
      (SheafOfModules.GradedAlgebra.smallPieceEquiv s.algebra n U).toEquiv _).2
      (s.sections_hasCardinalLT n U)

/-- The site of `s.shrink` is the site of `s`. -/
@[simp] theorem shrink_site : s.shrink.site = s.site := rfl
/-- The base of `s.shrink` is the base of `s`. -/
@[simp] theorem shrink_base : s.shrink.base = s.base := rfl
/-- The algebraic space of `s.shrink` is the algebraic space of `s`. -/
@[simp] theorem shrink_space : s.shrink.space = s.space := rfl
/-- The graded algebra of `s.shrink` is the re-presented algebra `smallAlgebra`. -/
theorem shrink_algebra : s.shrink.algebra = s.smallAlgebra := rfl

end AlgebraicGeometry.Space.RelativeProjSituation
