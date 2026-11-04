module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.LocalInvertibility
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekChartConsequences
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentPerfectDual
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualIsPerfect
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectDual
public import StacksFrontier.CategoryTheory.Monoidal.RigidAdjunction
public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.AlgebraicGeometry.Duality.GlobalDualizingUniqueness
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackBraided

/-!
# The relative dualizing complex of a proper flat Gorenstein morphism is invertible

Let `S` be a Noetherian scheme and `g : Y ⟶ S` a flat proper Gorenstein morphism. Then the
relative dualizing complex `ω^•_{Y/S} = a_g(𝒪_S)` of [Stacks, Tag 0B6S] (where `a_g` is the right
adjoint of `Rg_*` of [Stacks, Tag 0A9E]) is an invertible object of `D_QCoh(𝒪_Y)`. This is the
input "`ω^•_{Y/S}` is an invertible object of the derived category, see [Stacks, Tag 0C08]" of
the proof of [Stacks, Tag 0FYX].

The proof: `g` is a morphism of `FTS S` and `Y` itself is a compactification of `Y` over `S`, at
which `g^! = a_g`; by [Stacks, Tag 0C08] every point of `Y` has a neighbourhood on which `g^!𝒪_S`
is invertible; invertibility is local
(`Stacks.Duality.isInvertible_of_forall_exists_isInvertible_restrictFunctor`); an invertible
object is perfect ([Stacks, Tag 0FPD]), so it has its derived dual as a dual in `D_QCoh(𝒪_Y)`,
and the evaluation of that duality, being one for an invertible object of `D(𝒪_Y)`, is an
isomorphism.

## Main results

* `CategoryTheory.MonoidalCategory.isInvertible_of_isInvertible_map` — a fully faithful monoidal
  functor reflects invertibility of an object with a dual.
* `Stacks.Duality.isInvertible_twistedInverseImage_unit_of_isGorenstein` — the result.

## References

* [Stacks Project, Tag 0C08](https://stacks.math.columbia.edu/tag/0C08)
* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
* [Stacks Project, Tag 0FYX](https://stacks.math.columbia.edu/tag/0FYX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Duality.DerivedPushforward

universe u

namespace CategoryTheory.MonoidalCategory

/-- **A fully faithful monoidal functor reflects invertibility of an object with a dual.** If
`(X, Y)` is an exact pairing in a braided monoidal category and `F X` is invertible, then the
evaluation of the mapped pairing is an isomorphism, hence so is the evaluation `Y ⊗ X ⟶ 𝟙` of
`(X, Y)`, and `X` is invertible. -/
theorem isInvertible_of_isInvertible_map {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.Full] [F.Faithful] (X Y : C) [ExactPairing X Y]
    (h : IsInvertible (F.obj X)) : IsInvertible X := by
  let := ExactPairing.map F X Y
  obtain ⟨H⟩ := h
  have : (tensorRight (F.obj X)).IsEquivalence := H.tensorRightEquivalence.isEquivalence_functor
  have : IsIso (Functor.LaxMonoidal.μ F Y X ≫ F.map (ε_ X Y) ≫ Functor.OplaxMonoidal.η F) :=
    ExactPairing.isIso_evaluation (F.obj X) (F.obj Y)
  have : IsIso (F.map (ε_ X Y)) := by
    have : IsIso (F.map (ε_ X Y) ≫ Functor.OplaxMonoidal.η F) :=
      IsIso.of_isIso_comp_left (Functor.LaxMonoidal.μ F Y X) _
    exact IsIso.of_isIso_comp_right _ (Functor.OplaxMonoidal.η F)
  have : IsIso (ε_ X Y) := isIso_of_fully_faithful F _
  exact isInvertible_of_isIso_tensorHom_unit (ε_ X Y) inferInstance

end CategoryTheory.MonoidalCategory

namespace Stacks.Duality

variable {Y : Scheme.{u}}

/-- **An object of `D_QCoh(𝒪_Y)` invertible in `D(𝒪_Y)` is invertible in `D_QCoh(𝒪_Y)`.** It is
perfect ([Stacks, Tag 0FPD]), so it has its derived dual as a dual in `D_QCoh(𝒪_Y)`
(`Stacks.Duality.exactPairingPerfectDual`), and the inclusion is a fully faithful monoidal
functor. -/
theorem isInvertible_quasiCoherentDerivedCategory_of_isInvertible
    (ω : quasiCoherentDerivedCategory Y)
    (h : letI := Scheme.Modules.derivedMonoidal Y; IsInvertible ω.obj) :
    IsInvertible ω := by
  have hperf : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) ω.obj := by
    obtain ⟨N, ⟨p⟩⟩ := @IsInvertible.exists_exactPairing _ _
      (Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory Y.toRingedSpace) ω.obj h
    exact Stacks.Cohomology.LeftDualPerfect.isPerfect_of_exactPairing Y.toRingedSpace ω.obj N p
  let := exactPairingPerfectDual ω hperf
  let := Scheme.Modules.canonicalDerivedMonoidal Y
  have hc : IsInvertible ((ObjectProperty.ι _ : quasiCoherentDerivedCategory Y ⥤ _).obj ω) :=
    @MonoidalCategory.isInvertible_of_tensorComparison_of_braided _ _
      (Scheme.Modules.derivedMonoidal Y) _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Y.sheaf).toBraidedCategory
      (𝟭 _)
      (fun A B => ((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso
        Y.sheaf).app A).app B)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Y.sheaf) _ h
  exact isInvertible_of_isInvertible_map (ObjectProperty.ι _) ω (perfectDual ω hperf) hc

/-- **The relative dualizing complex of a flat proper Gorenstein morphism is invertible.** Let
`S` be Noetherian and `g : Y ⟶ S` flat, proper and Gorenstein. Then `ω^•_{Y/S} = a_g(𝒪_S)` is an
invertible object of `D_QCoh(𝒪_Y)`. -/
theorem isInvertible_twistedInverseImage_unit_of_isGorenstein {S : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian S] [QuasiSeparatedSpace S] (g : Y ⟶ S) [IsProper g] [Flat g]
    (hfib : ∀ s : S, IsLocallyNoetherian (g.fiber s)) (hG : g.IsGorenstein hfib)
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsInvertible
      ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj
        (𝟙_ (quasiCoherentDerivedCategory S))) := by
  let Ŷ : FTS S := FTS.mk g
  let Ŝ : FTS S := FTS.mk (𝟙 S)
  let ĝ : Ŷ ⟶ Ŝ := MorphismProperty.Over.homMk g (Category.comp_id g)
  let j : CompactificationOf (Over.mk ĝ.left) :=
    ⟨StructuredArrow.mk (Y := Over.mk g)
      (Over.homMk (U := Over.mk ĝ.left) (V := Over.mk g) (𝟙 Y) (Category.id_comp g)),
      ⟨inferInstanceAs (IsOpenImmersion (𝟙 Y)), inferInstanceAs (IsProper g)⟩⟩
  have : Flat ĝ.left := inferInstanceAs (Flat g)
  have hglob := isInvertible_of_forall_exists_isInvertible_restrictFunctor
    (relativeDualizingComplexObj ĝ j)
    fun y : Y => ((isGorensteinAt_iff_exists_isInvertible_upperShriek ĝ j).1 y).1 (hG y)
  refine isInvertible_quasiCoherentDerivedCategory_of_isInvertible _ ?_
  let := Scheme.Modules.derivedMonoidal Y
  exact MonoidalCategory.isInvertible_of_iso ((derivedPullbackIdIso Y).app _ ≪≫ eqToIso (by
    rw [tensorUnit_quasiCoherentDerivedCategory]; rfl)) hglob

end Stacks.Duality

end
