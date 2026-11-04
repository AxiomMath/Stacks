module

public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom.Canonical

/-!
# The canonical system of derived pullbacks of Situation 09RH

`AlgebraicGeometry.Space.DescentSituation.DerivedPullbackSystem` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom.lean` carries the derived pullbacks
`Lf_{i0}^*`, `Lf_{ji}^*`, `Lf_i^*`, `Lf_0^*` of Situation 09RH together with two comparison
isomorphisms, and `AlgebraicGeometry.Space.DescentSituation.IsHomColimit` is its colimit
statement.  The comparisons of such a system are unconstrained, so that statement is in general a
condition on them as well.  This file builds **the** system, whose comparisons are the canonical
ones of the coherent pseudofunctor `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` of
Stacks 06YY and 0D6D, and identifies its colimit statement with
`CategoryTheory.PullbackData.LimitSystem.IsColim` for the stages of Situation 09RH over `X₀` —
the form in which the closure properties of
`StacksFrontier/CategoryTheory/PullbackData/LimitHomSystem.lean` are available.

## Main definitions

* `AlgebraicGeometry.Space.derivedModulePullbackCanonical` is the derived pullback of
  `𝒪`-modules along a morphism of algebraic spaces as a
  `AlgebraicGeometry.Space.DerivedModulePullback`.
* `AlgebraicGeometry.Space.DescentSituation.canonicalDerivedPullbackSystem` is the system of
  derived pullbacks of Situation 09RH with the canonical comparisons.

## Main results

* `CategoryTheory.Functor.mapHomotopyCategory_congr`: equal additive functors induce the same
  functor on the unbounded homotopy categories.
* `CategoryTheory.Functor.conjHom_symm`: conjugation by the inverse of a comparison, written
  out.
* `CategoryTheory.Functor.isLeftDerivedFunctor_comp_eqToHom`: a total left derived functor read
  through an equality of the functors being derived.
* `AlgebraicGeometry.Space.modulePullbackOnHomotopy_eq`: the two spellings of degreewise inverse
  image of `𝒪`-modules followed by localization agree.
* `AlgebraicGeometry.Space.DescentSituation.isHomColimit_canonicalDerivedPullbackSystem_iff`:
  the colimit statement of Stacks 09RI for the canonical system is the colimit statement for the
  stages of Situation 09RH as a system over `X₀`.

## Implementation notes

No derived-category model is installed here.  Every object this file speaks about —
`AlgebraicGeometry.Space.derivedModules`,
`AlgebraicGeometry.Space.DerivedModulePullback`,
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` and
`AlgebraicGeometry.Space.DescentSituation.DerivedPullbackSystem` — carries its model in its own
type, so the statements below inherit it.

The derived pullback of Stacks 06YY is constructed at the category of `𝒪`-modules of the small
étale ringed *topos*, and Stacks 09RI is stated at the category of `𝒪`-modules of the small étale
ringed *site*.  The two are definitionally but not reducibly equal, so the preadditive structures
instance resolution finds at them differ and `(modulePullback B S hS f).Additive` does not
synthesize at the topos spelling; the same obstruction is recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDerivedModulePullback.lean`.  The two additivity
witnesses are therefore passed by name to
`CategoryTheory.Functor.mapHomotopyCategory_congr`.

`AlgebraicGeometry.Space.derivedModulePullbackCanonical` takes its functor in the spelling
`(smallEtaleDerivedPullbackData B S hS).pull f` rather than the equal
`AlgebraicGeometry.Space.derivedPull`.  The two are interchangeable at the level of functors, but
an equation between morphisms of a derived category whose two sides are formed with different
spellings of the functor sends the kernel into the unfolding of the total left derived functor.
For the same reason the two shapes in which the comparison is conjugated are reconciled by
`CategoryTheory.Functor.conjHom_symm`, whose functors are free variables, rather than by
unfolding `CategoryTheory.Functor.conjHom` at the derived pullbacks.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Functor

/-- Equal additive functors induce the same functor on the unbounded homotopy categories. -/
theorem mapHomotopyCategory_congr {ι : Type*} {C E : Type*} [Category* C] [Category* E]
    [Preadditive C] [Preadditive E] {F G : C ⥤ E} [iF : F.Additive] [iG : G.Additive] (h : F = G)
    (Φ : ComplexShape ι) : F.mapHomotopyCategory Φ = G.mapHomotopyCategory Φ := by
  subst h
  rfl

/-- **Conjugation by the inverse of a comparison, written out**: the conjugate of
`CategoryTheory.Functor.conjHom` by `e.symm` is the morphism read through `e` at the source and
at the target. -/
theorem conjHom_symm {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₁ ⋙ L ≅ P₂) {M N : C}
    (α : P₁.obj M ⟶ P₁.obj N) :
    (e.app M).inv ≫ L.map α ≫ (e.app N).hom = conjHom e.symm α :=
  rfl

/-- A total left derived functor stays one when its counit is composed with the transport along
an equality of the functors being derived. -/
theorem isLeftDerivedFunctor_comp_eqToHom {C D H : Type*} [Category* C] [Category* D]
    [Category* H] {L : C ⥤ D} {F G : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    {W : MorphismProperty C} [L.IsLocalization W] (hLF : LF.IsLeftDerivedFunctor α W)
    (h : F = G) : LF.IsLeftDerivedFunctor (α ≫ eqToHom h) W := by
  subst h
  rw [eqToHom_refl, Category.comp_id]
  exact hLF

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Degreewise inverse image of `𝒪`-modules along a morphism of algebraic spaces followed by
localization, read at the small étale ringed topos and at the small étale ringed site, is the
same functor. -/
theorem modulePullbackOnHomotopy_eq {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    smallEtaleModulePullbackOnHomotopy B S hS f = modulePullbackOnHomotopy B S hS f := by
  unfold smallEtaleModulePullbackOnHomotopy modulePullbackOnHomotopy
    Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy
  congr 1
  exact Functor.mapHomotopyCategory_congr
    (iF := modulePullbackDataTopos_additive B S hS f)
    (iG := (inferInstance : (modulePullback B S hS f).Additive))
    (toModulesHom_pullbackModules_eq_modulePullback B S hS f) (ComplexShape.up ℤ)

/-- **The derived pullback of `𝒪`-modules along a morphism of algebraic spaces as a
`AlgebraicGeometry.Space.DerivedModulePullback`**: the inverse image of the pseudofunctor of
Stacks 06YY, with the canonical comparison exhibiting it as a total left derived functor of the
inverse image of Stacks 03LU. -/
def derivedModulePullbackCanonical {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    DerivedModulePullback B S hS f where
  functor := (smallEtaleDerivedPullbackData B S hS).pull f
  counit := haveI := hasDerivedModulePullbacks B S hS f
    smallEtaleDerivedModulePullbackComparison B S hS f ≫
      eqToHom (modulePullbackOnHomotopy_eq B S hS f)
  isLeftDerived := by
    have := hasDerivedModulePullbacks B S hS f
    exact Functor.isLeftDerivedFunctor_comp_eqToHom _
      (smallEtaleDerivedModulePullbackComparison B S hS f)
      (W := smallEtaleModuleQuasiIso B S hS Y) inferInstance
      (modulePullbackOnHomotopy_eq B S hS f)

namespace DescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- **The system of derived pullbacks of Situation 09RH with the canonical comparisons**: the
derived pullback of Stacks 06YY along every morphism the tag mentions, and for the two
comparisons the composition isomorphisms of the coherent pseudofunctor
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` at the factorisations
`f_{ji} ≫ f_{i0} = f_{j0}` and `f_i ≫ f_{i0} = f_0`. -/
def canonicalDerivedPullbackSystem : D.DerivedPullbackSystem where
  stagePullback i := derivedModulePullbackCanonical B S hS (D.transition i.2)
  transPullback i j h :=
    derivedModulePullbackCanonical B S hS (D.transition (show i.1 ≤ j.1 from h))
  projPullback i := derivedModulePullbackCanonical B S hS (D.projection i.1)
  limitPullback := derivedModulePullbackCanonical B S hS (D.projection D.base)
  transComp _ _ h := ((smallEtaleDerivedPullbackData B S hS).triangle
    (D.limitSystem.transition_toBase h)).symm
  projComp i := ((smallEtaleDerivedPullbackData B S hS).triangle
    (D.limitSystem.proj_toBase i)).symm

variable (E₀ K₀ : derivedModules B S hS (D.stage D.base))

/-- The transition comparison of the canonical system is the composition comparison of the
pseudofunctor at the factorisation `f_{ji} ≫ f_{i0} = f_{j0}`. -/
theorem canonicalDerivedPullbackSystem_transComp (i j : D.Stages) (h : i ≤ j) :
    D.canonicalDerivedPullbackSystem.transComp i j h =
      ((smallEtaleDerivedPullbackData B S hS).triangle
        (D.limitSystem.transition_toBase h)).symm :=
  rfl

/-- The projection comparison of the canonical system is the composition comparison of the
pseudofunctor at the factorisation `f_i ≫ f_{i0} = f_0`. -/
theorem canonicalDerivedPullbackSystem_projComp (i : D.Stages) :
    D.canonicalDerivedPullbackSystem.projComp i =
      ((smallEtaleDerivedPullbackData B S hS).triangle (D.limitSystem.proj_toBase i)).symm :=
  rfl

/-- The transition maps of Stacks 09RI for the canonical system are those of the system of
stages of Situation 09RH over `X₀`. -/
theorem homTransition_canonical_eq :
    homTransition D.canonicalDerivedPullbackSystem E₀ K₀ =
      D.limitSystem.trans (smallEtaleDerivedPullbackData B S hS) E₀ K₀ := by
  funext i j h g
  exact Functor.conjHom_symm _ g

/-- The maps to the limit of Stacks 09RI for the canonical system are those of the system of
stages of Situation 09RH over `X₀`. -/
theorem homProjection_canonical_eq :
    homProjection D.canonicalDerivedPullbackSystem E₀ K₀ =
      D.limitSystem.projHom (smallEtaleDerivedPullbackData B S hS) E₀ K₀ := by
  funext i g
  exact Functor.conjHom_symm _ g

/-- **The colimit statement of Stacks 09RI for the canonical system is the colimit statement for
the stages of Situation 09RH as a system over `X₀`**: the transition maps and the maps to the
limit of `AlgebraicGeometry.Space.DescentSituation.canonicalDerivedPullbackSystem` are those of
`CategoryTheory.PullbackData.LimitSystem`. -/
theorem isHomColimit_canonicalDerivedPullbackSystem_iff :
    IsHomColimit D.canonicalDerivedPullbackSystem E₀ K₀ ↔
      D.limitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) E₀ K₀ := by
  show Stacks.IsStagesColimit (homTransition D.canonicalDerivedPullbackSystem E₀ K₀)
      (homProjection D.canonicalDerivedPullbackSystem E₀ K₀) ↔
    Stacks.IsStagesColimit (D.limitSystem.trans (smallEtaleDerivedPullbackData B S hS) E₀ K₀)
      (D.limitSystem.projHom (smallEtaleDerivedPullbackData B S hS) E₀ K₀)
  rw [homTransition_canonical_eq, homProjection_canonical_eq]
  exact Iff.rfl

end DescentSituation

end AlgebraicGeometry.Space

end
