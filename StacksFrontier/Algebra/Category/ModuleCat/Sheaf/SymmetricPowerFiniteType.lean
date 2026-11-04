module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of the symmetric powers of a sheaf of modules

Let `(X, 𝒪_X)` be a ringed space and `F` a sheaf of `𝒪_X`-modules of finite presentation. Then
every symmetric power `Symⁿ F` is again of finite presentation. This is clause (3) of Stacks Tag
01CK for the symmetric powers, and it is the symmetric half of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType`, which does the exterior
half.

The mathematics is Tag 01CJ, already available: an exact presentation of `F` by free modules over
an open presents `Symⁿ F` over that *same* open, by free modules whose index types are built
from the index types of the given presentation
(`Stacks.SheafOfModules.exists_free_symmetricPower_presentation`). When the given presentation is
finite the index types produced for `Symⁿ F` are a finite product and the set of degree-`n`
multidegrees in a finite set, so they are finite as well; those are the two implications
`Finite I₂ → Finite I₁ → Finite J` and `Finite I₁ → Finite K` that
`exists_free_symmetricPower_presentation` already carries. Everything else is the bookkeeping of
finiteness along the constructions by which
`Stacks.SheafOfModules.nonempty_presentation_symmetricPower_over` builds a presentation of
`(Symⁿ F)|_U` out of one of `F|_U`, and every transfer it needs is already proved in
`ExteriorPowerFiniteType` in a form that is not exterior-specific:
`Stacks.SheafOfModules.presentationOfIsCokernelFree_isFinite`, `presentationOfIso_isFinite`,
`presentation_isFinite_map`, `presentationUnit_isFinite` and
`presentationOfOpenSubspaceIso_isFinite`.

## Main results

* `Stacks.SheafOfModules.exists_isFinite_presentation_symmetricPower`: a finite presentation of a
  sheaf of modules on a ringed space gives a finite presentation of each of its symmetric powers.
* `Stacks.SheafOfModules.exists_isFinite_presentation_symmetricPower_over`: the same over an
  open, for the restriction of a symmetric power computed on the whole space.
* `Stacks.SheafOfModules.isFinitePresentation_symmetricPower`: **clause (3) of Tag 01CK for the
  symmetric powers** — each symmetric power of a sheaf of modules of finite presentation on a
  ringed space is of finite presentation.

## Implementation notes

**The degree-zero piece is not a field of the bundle.** For the exterior algebra the
identification of degree zero with the structure sheaf is
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPieceZeroIsoUnit`; for the symmetric
algebra it is not carried by the bundle, and the composite used here is the one
`Stacks.SheafOfModules.nonempty_presentation_symmetricPower` uses —
`SheafOfModules.symmetricPieceIso` followed by
`SheafOfModules.sectionwiseSymmetricPieceZeroIso`.

**Clause (2) is not claimed.** Finite presentation implies finite type, so
`Stacks.SheafOfModules.isFinitePresentation_symmetricPower` gives finite type of `Symⁿ F` for
`F` of finite presentation; but clause (2) of Tag 01CK assumes only that `F` is of finite type,
which is strictly weaker, so that consequence is not that clause and is not tagged as one. The
same holds for the exterior statement
`Stacks.SheafOfModules.isFiniteType_exteriorPower` in `ExteriorPowerFiniteType`. The clause
itself is `Stacks.SheafOfModules.isFiniteType_symmetricPower` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerLocalGenerators`, which needs only the
surjectivity half of Tag 01CJ and no presentation at all.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

-- The structure sheaf of rings of a ringed space is one definition whose body stops at an
-- explicit-constructor projection, so reaching `toRingCat J X.sheaf` from it needs these two
-- Mathlib definitions unfoldable in the file.
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.SheafOfModules

/-- **A finite presentation of a sheaf of modules on a ringed space presents every symmetric
power of it finitely.** This is the finite refinement of
`Stacks.SheafOfModules.nonempty_presentation_symmetricPower`: in positive degree the two index
types produced by Tag 01CJ are finite as soon as the given ones are, which is the content of the
two implications in `Stacks.SheafOfModules.exists_free_symmetricPower_presentation`, and in
degree zero the symmetric power is the structure sheaf. -/
theorem exists_isFinite_presentation_symmetricPower {Y : RingedSpace.{u, u}}
    {M : _root_.SheafOfModules.{u} (structureSheafRing Y)}
    (q : M.Presentation) [hq : q.IsFinite]
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology Y.carrier) M) (n : ℕ) :
    ∃ p : (A.symmetricPower n).Presentation, p.IsFinite := by
  let _ : HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u} := inferInstance
  let _ : (Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨presentationOfIso
      ((_root_.SheafOfModules.symmetricPieceIso M A.symmetric A.symmetricGenerator
        A.symmetric_isSymmetricAlgebra 0).symm ≪≫
        _root_.SheafOfModules.sectionwiseSymmetricPieceZeroIso
          (Opens.grothendieckTopology Y.carrier) (𝟙 Y.sheaf.obj) M.val).symm presentationUnit,
      inferInstance⟩
  · obtain ⟨T, ιJ, ιK, hJ, hK, -, -, hT₃, hex, hepi, ⟨e₁⟩, ⟨e₂⟩⟩ :=
      exists_free_symmetricPower_presentation
        (S := ShortComplex.mk q.relationsHom q.generators.π q.relationsHom_comp_π)
        (ShortComplex.exact_of_g_is_cokernel _ q.isColimitRelationsHom) q.generators.epi
        (_root_.SheafOfModules.ringedSpaceAlgebras Y _) A
        q.relations.I q.generators.I (Iso.refl _) (Iso.refl _) n hn
    have := hepi
    have : Finite ιJ := hJ inferInstance inferInstance
    have : Finite ιK := hK inferInstance
    rw [← hT₃]
    exact ⟨_root_.SheafOfModules.presentationOfIsCokernelFree
      (e₁.inv ≫ T.f ≫ e₂.hom) (e₂.inv ≫ T.g) (by simp [T.zero])
      (IsCokernel.ofIso _ hex.gIsCokernel _ e₁ e₂ (Iso.refl _) (by simp) (by simp)),
      inferInstance⟩

section Over

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  (F : _root_.SheafOfModules.{u} (structureSheafRing X))
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)

/-- **A finite presentation of `F` over an open presents every symmetric power of `F` finitely
over that same open.** This is the finite refinement of
`Stacks.SheafOfModules.nonempty_presentation_symmetricPower_over`, and as there the uniformity in
`n` matters: one open presents every degree, with no further shrinking. -/
theorem exists_isFinite_presentation_symmetricPower_over
    (p : (F.over U).Presentation) [hp : p.IsFinite] (n : ℕ) :
    ∃ r : ((A.symmetricPower n).over U).Presentation, r.IsFinite := by
  have hB := _root_.SheafOfModules.isSymmetricAlgebra_sectionwiseSymmetricAlgebra_val
    (J := (Opens.grothendieckTopology X.carrier).over U) (Osharp := X.sheaf.over U) (F.over U)
  obtain ⟨q, hq⟩ := exists_isFinite_presentation_symmetricPower
    (p.map (openSubspaceEquiv U).functor
      (U.sheafOfModulesEquivOverUnit (structureSheafRing X)).symm)
    (openSubspaceAlgebras U F) n
    (hq := presentation_isFinite_map p (openSubspaceEquiv U).functor
      (U.sheafOfModulesEquivOverUnit (structureSheafRing X)).symm)
  exact ⟨presentationOfIso
    (symmetricPowerOverIso F U n A.symmetric A.symmetricGenerator
      A.symmetric_isSymmetricAlgebra _ _ hB).symm
    (presentationOfOpenSubspaceIso U (symmetricPowerPushforwardIso
      (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
      (Jt := (Opens.grothendieckTopology X.carrier).over U) (Osharp := X.sheaf.over U)
      (F.over U) n _ _ hB (openSubspaceAlgebras U F).symmetric
      (openSubspaceAlgebras U F).symmetricGenerator
      (openSubspaceAlgebras U F).symmetric_isSymmetricAlgebra) q),
    presentationOfIso_isFinite _ _
      (hP := presentationOfOpenSubspaceIso_isFinite U _ q (hP := hq))⟩

end Over

section Conclusions

variable {X : RingedSpace.{u, u}}
  (F : _root_.SheafOfModules.{u} (structureSheafRing X))
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)

/-- **Each symmetric power of a sheaf of modules of finite presentation on a ringed space is of
finite presentation.** This is clause (3) of [Stacks, Tag 01CK] for the symmetric powers. The
covering family is the one that presents `F` finitely; no degree needs a smaller open, because
`Stacks.SheafOfModules.exists_isFinite_presentation_symmetricPower_over` presents every degree
finitely over that same open. -/
@[stacks 01CK "symmetric powers of a module of finite presentation", ega "II 1.7.7" "special case"]
theorem isFinitePresentation_symmetricPower [F.IsFinitePresentation] (n : ℕ) :
    (A.symmetricPower n).IsFinitePresentation := by
  obtain ⟨c, hc⟩ :=
    _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData.{u, u, u} F
  have hp : ∀ i, ∃ r : ((A.symmetricPower n).over (c.X i)).Presentation, r.IsFinite := fun i =>
    exists_isFinite_presentation_symmetricPower_over (c.X i) F A (c.presentation i) n
      (hp := hc.isFinite_presentation i)
  let q : _root_.SheafOfModules.QuasicoherentData.{u, u, u, u} (A.symmetricPower n) :=
    { I := c.I
      X := c.X
      coversTop := c.coversTop
      presentation := fun i => (hp i).choose }
  have hq : _root_.SheafOfModules.QuasicoherentData.IsFinitePresentation.{u, u, u, u} q := by
    constructor
    intro i
    exact (hp i).choose_spec
  constructor
  exact ⟨q, hq⟩

end Conclusions

end Stacks.SheafOfModules

end
