module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekAffineCharts
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingBaseChange.FibreDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimension

/-!
# `f_new^! 𝒪_Y` on an open of the source separated over the target

In Situation [Stacks, Tag 0AU4], let `f : X ⟶ Y` be a morphism of schemes of finite type over
`S`, not necessarily separated, and let `ω_X^•`, `ω_Y^•` be the dualizing complexes normalized
relative to `ω_S^•`. For an open `V ⊆ X` such that `V → Y` is separated (for instance an affine
open), the restriction of `f_new^! 𝒪_Y = D_X(Lf^* D_Y(𝒪_Y))` to `V` is

`(f_new^! 𝒪_Y)|_V ≅ (V → Y)_new^! 𝒪_Y ≅ (V → Y)^! 𝒪_Y`,

the first isomorphism because `D_X` and `Lf^*` commute with restriction to opens and
`ω_X^•|_V = ω_V^•`, the second by the closing remark of [Stacks, Tag 0AUE] for the separated
morphism `V → Y`, viewed as a morphism of `FTS_Y`. This is the reduction "the proof reduces
immediately to the affine case and then `f^! = f_new^!` by Lemma 0AUE" of
[Stacks, Tag 0BV9].

## Main definitions

* `Stacks.Duality.homologyPullIsoOfDegree`: `H^i` at the standard model commutes with
  restriction to an open.
* `Stacks.Duality.NormalizedOnOpens.newShriekStructureSheaf`: `f_new^! 𝒪_Y` at the standard
  model.
* `Stacks.Duality.NormalizedOnOpens.newShriekStructureSheafRestrictIso`:
  `(f_new^! 𝒪_Y)|_V ≅ (V → Y)^! 𝒪_Y`.
* `Stacks.Duality.NormalizedOnOpens.newShriekHomologyRestrictIso`: the same on cohomology
  sheaves, with `(V → Y)^! 𝒪_Y` read at the locally small model.

## Main results

* `Stacks.Duality.NormalizedOnOpens.nontrivial_stalk_homology_newShriek_iff`: the stalk of
  `H^i(f_new^! 𝒪_Y)` at a point of `V` is that of `H^i((V → Y)^! 𝒪_Y)`.

## References

* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0BV9](https://stacks.math.columbia.edu/tag/0BV9)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std comparison plusCoh pull
  stdMonoidal stdSymmetric stdMonoidalClosed)
open CategoryTheory.MonoidalClosed

/-- `H^i` at the standard model commutes with restriction to an open. -/
def homologyPullIsoOfDegree {X : Scheme.{u}} (V : X.Opens) (K : Std X) (i : ℤ) :
    (@DerivedCategory.homologyFunctor V.toScheme.Modules _ _
      (PerfectApproximation.standardModel V.toScheme) i).obj ((pull V.ι).obj K) ≅
      ((@DerivedCategory.homologyFunctor X.Modules _ _
        (PerfectApproximation.standardModel X) i).obj K).restrict V.ι :=
  letI := PerfectApproximation.standardModel X
  letI := PerfectApproximation.standardModel V.toScheme
  (DerivedCategory.homologyFunctor V.toScheme.Modules i).mapIso
      ((Scheme.Modules.derivedRestrictIsoDerivedPullback V.ι).app K).symm ≪≫
    ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategoryHomologyIso i).app K

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} (f : X ⟶ Y) {q : Y ⟶ S} {p : X ⟶ S}
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)

attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed in
/-- `f_new^! 𝒪_Y = D_X(Lf^* D_Y(𝒪_Y))`, at the standard model, with `ω_X^•` and `ω_Y^•` the
complexes `𝒦X` and `𝒦Y` normalized relative to `ω_S^•`. -/
abbrev newShriekStructureSheaf : Std X :=
  (fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).obj (structureStd Y)

variable {f} (hpe : f ≫ q = p) (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)

attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed in
/-- **`f_new^! 𝒪_Y` on an open separated over the target.** For an open `V ⊆ X` with `V → Y`
separated, `(f_new^! 𝒪_Y)|_V ≅ (V → Y)^! 𝒪_Y`, the upper shriek of `V → Y` as a morphism of
`FTS_Y` at the compactification `c`, read at the standard model: restriction commutes with
`D_X` and `Lf^*`, the normalized complex restricts to the normalized complex, and
`(V → Y)_new^! = (V → Y)^!` on `D^+_Coh` by the closing remark of [Stacks, Tag 0AUE]. -/
def newShriekStructureSheafRestrictIso (V : X.Opens) (hV : IsShriekable (V.ι ≫ f)) :
    haveI := hq.source_noetherian
    (pull V.ι).obj (newShriekStructureSheaf c f 𝒦X 𝒦Y) ≅
      (UpperShriekDuality.upperShriekStd (ftsHomSelf hV) (c _ hV)).obj
        ⟨structureStd Y, plusCoh_structureStd Y⟩ :=
  haveI := hq.source_noetherian
  (fNewShriekRestrictIso V.ι f (V.ι ≫ f) rfl (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).app
      (structureStd Y) ≪≫
    (Functor.isoWhiskerLeft ((dualInto (stdComplex c 𝒦Y)).rightOp ⋙ (pull (V.ι ≫ f)).op)
      (dualIntoMapIso (stdComplexRestrictIso c 𝒦X V).symm)).app (structureStd Y) ≪≫
    ((upperShriekStdIsoFNewShriek c (comp_structure_ι hpe V) hωS hV (𝒦X.restrict V) 𝒦Y).app
      ⟨structureStd Y, plusCoh_structureStd Y⟩).symm

/-- The cohomology sheaves of `(V → Y)^! 𝒪_Y` at the two models of the derived category. -/
def upperShriekStdStructureHomologyIso (V : X.Opens) (hV : IsShriekable (V.ι ≫ f)) (i : ℤ) :
    haveI := hq.source_noetherian
    (@DerivedCategory.homologyFunctor V.toScheme.Modules _ _
      (PerfectApproximation.standardModel V.toScheme) i).obj
        ((UpperShriekDuality.upperShriekStd (ftsHomSelf hV) (c _ hV)).obj
          ⟨structureStd Y, plusCoh_structureStd Y⟩) ≅
      (DerivedCategory.homologyFunctor (ftsOf (V.ι ≫ f) hV.separatedFiniteType).left.Modules i).obj
        (relativeDualizingComplexObj (ftsHomSelf hV) (c _ hV)) :=
  haveI := hq.source_noetherian
  (PerfectApproximation.homologyStandardIso _ i).symm

/-- **The cohomology sheaves of `f_new^! 𝒪_Y` on an open separated over the target.** For an
open `V ⊆ X` with `V → Y` separated, `H^i(f_new^! 𝒪_Y)|_V ≅ H^i((V → Y)^! 𝒪_Y)`, the right hand
side at the locally small model. -/
def newShriekHomologyRestrictIso (V : X.Opens) (hV : IsShriekable (V.ι ≫ f)) (i : ℤ) :
    haveI := hq.source_noetherian
    ((@DerivedCategory.homologyFunctor X.Modules _ _ (PerfectApproximation.standardModel X)
        i).obj (newShriekStructureSheaf c f 𝒦X 𝒦Y)).restrict V.ι ≅
      (DerivedCategory.homologyFunctor (ftsOf (V.ι ≫ f) hV.separatedFiniteType).left.Modules i).obj
        (relativeDualizingComplexObj (ftsHomSelf hV) (c _ hV)) :=
  haveI := hq.source_noetherian
  (homologyPullIsoOfDegree V _ i).symm ≪≫
    (@DerivedCategory.homologyFunctor V.toScheme.Modules _ _
      (PerfectApproximation.standardModel V.toScheme) i).mapIso
        (newShriekStructureSheafRestrictIso c 𝒦X 𝒦Y hpe hωS V hV) ≪≫
    upperShriekStdStructureHomologyIso c (hq := hq) V hV i

include hpe hωS in
/-- **The stalks of `H^i(f_new^! 𝒪_Y)` at points of an open separated over the target** are the
stalks of `H^i((V → Y)^! 𝒪_Y)`. -/
theorem nontrivial_stalk_homology_newShriek_iff (V : X.Opens) (hV : IsShriekable (V.ι ≫ f))
    (i : ℤ) (x : V.toScheme) :
    haveI := hq.source_noetherian
    Nontrivial (((@DerivedCategory.homologyFunctor X.Modules _ _
        (PerfectApproximation.standardModel X) i).obj
          (newShriekStructureSheaf c f 𝒦X 𝒦Y)).presheaf.stalk (V.ι x)) ↔
      Nontrivial (((DerivedCategory.homologyFunctor
        (ftsOf (V.ι ≫ f) hV.separatedFiniteType).left.Modules i).obj
          (relativeDualizingComplexObj (ftsHomSelf hV) (c _ hV))).presheaf.stalk x) := by
  have := hq.source_noetherian
  let F := (@DerivedCategory.homologyFunctor X.Modules _ _
    (PerfectApproximation.standardModel X) i).obj (newShriekStructureSheaf c f 𝒦X 𝒦Y)
  have e₁ : ((Scheme.Modules.restrictFunctor V.ι).obj F).presheaf.stalk x ≅
      F.presheaf.stalk (V.ι x) :=
    (Scheme.Modules.restrictStalkNatIso V.ι x).app F
  have e₂ : ((Scheme.Modules.restrictFunctor V.ι).obj F).presheaf.stalk x ≅
      ((DerivedCategory.homologyFunctor (ftsOf (V.ι ≫ f) hV.separatedFiniteType).left.Modules i).obj
        (relativeDualizingComplexObj (ftsHomSelf hV) (c _ hV))).presheaf.stalk x :=
    (TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso
      ((Scheme.Modules.toPresheaf V.toScheme).mapIso
        (newShriekHomologyRestrictIso c 𝒦X 𝒦Y hpe hωS V hV i))
  exact (nontrivial_iff_of_abIso e₁).symm.trans (nontrivial_iff_of_abIso e₂)

end NormalizedOnOpens

end Stacks.Duality

end
