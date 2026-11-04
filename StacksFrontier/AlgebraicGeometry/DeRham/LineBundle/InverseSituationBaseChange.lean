module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinate
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceChangeModule
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceHomEquivId
public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic

/-!
# The line bundle of an invertible module commutes with base change

Let `g : Y' ⟶ Y` be an arbitrary morphism of schemes and `M` an invertible `𝒪_Y`-module, and let
`M' = g^*M` be its pullback, which is again invertible. Write `q : L(M) ⟶ Y` for the line bundle
of `M` — the total space of `M^{⊗ -1}`, `Stacks.LineBundle.lineBundleSpace` — and
`q' : L(M') ⟶ Y'` for the line bundle of `M'`. This file produces the canonical morphism
`β : L(M') ⟶ L(M)` over `g` and shows that the square it sits in is cartesian.

## Main definitions

* `Stacks.LineBundle.inverseSituationPullbackIso`: the base change of the inverse,
  `g^*(M^{⊗ -1}) ≅ (g^*M)^{⊗ -1}`.
* `Stacks.LineBundle.inverseSituationBaseChangeIso`: the resulting identification of `L(M')` with
  the total space of the base-changed situation.
* `Stacks.LineBundle.pushforwardTransposeEquiv`: the transposition of fibrewise functionals
  across the base change.
* `Stacks.LineBundle.pairBaseChange`: that transposition, read on a pair in the functor of
  points.
* `Stacks.LineBundle.totalSpaceBaseChange`: the canonical morphism `β : L(M') ⟶ L(M)`.

## Main results

* `Stacks.LineBundle.totalSpaceBaseChange_comp_lineBundleProj`: the canonical morphism lies over
  `g`.
* `Stacks.LineBundle.existsUnique_lift_totalSpaceBaseChange`: a point of `L(M)` and a point of
  `Y'` agreeing over `Y` lift uniquely to a point of `L(g^*M)`.
* `Stacks.LineBundle.isPullback_totalSpaceBaseChange`: the square is cartesian, so the line
  bundle of the pulled-back module is the fibre product `Y' ×_Y L(M)`.
* `Stacks.LineBundle.totalSpaceHomEquiv_comp_totalSpaceBaseChange`: composing a point of `L(M')`
  with the canonical morphism transposes that point.
* `Stacks.LineBundle.totalSpaceHomEquiv_totalSpaceBaseChange`: the degree-one inclusion
  `M^{⊗ -1} ⟶ q_* 𝒪_{L(M)}`, pushed along the canonical morphism, is the transposition across the
  base change of the degree-one inclusion of the line bundle of `g^*M`.

## References

* [Stacks Project, Tag 01LS](https://stacks.math.columbia.edu/tag/01LS)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.LineBundle

variable {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (M : Y.Modules)
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

/-! ### The two situations and the comparison of their modules -/

/-- The base change of the inverse, `g^*(M^{⊗ -1}) ≅ (g^*M)^{⊗ -1}`, between the modules of the
two line-bundle situations. -/
def inverseSituationPullbackIso :
    (Scheme.Modules.pullback g).obj (inverseSituation Y M).L ≅
      (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L :=
  Stacks.ProjBundleInverseBaseChange.pullbackTensorPowerNegOneIso g M

/-- The inverse of the pulled-back module is invertible, read on the scheme of the base-changed
situation. -/
theorem isInvertible_baseChange_inverse :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      ((inverseSituation Y M).baseChange g).X.sheaf.obj
      ((inverseSituation Y M).baseChange g).X.ringCatSheaf.property
      (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L :=
  Situation.invertible (inverseSituation Y' ((Scheme.Modules.pullback g).obj M))

/-- The identification of the line bundle of `g^*M` with the total space of the base-changed
situation, along the base change of the inverse. -/
def inverseSituationBaseChangeIso :
    lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M) ≅
      ((inverseSituation Y M).baseChange g).totalSpace :=
  haveI := isInvertible_baseChange_inverse g M
  ((inverseSituation Y M).baseChange g).totalSpaceIsoOfIso
    (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L
    (inverseSituationPullbackIso g M)

/-- The identification of the two total spaces is one of schemes over `Y'`. -/
theorem inverseSituationBaseChangeIso_hom_comp_totalSpaceToBase :
    (inverseSituationBaseChangeIso g M).hom ≫
        ((inverseSituation Y M).baseChange g).totalSpaceToBase =
      lineBundleProj Y' ((Scheme.Modules.pullback g).obj M) :=
  have := isInvertible_baseChange_inverse g M
  ((inverseSituation Y M).baseChange g).totalSpaceIsoOfIso_hom_comp_totalSpaceToBase
    (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L
    (inverseSituationPullbackIso g M)

/-! ### The transposition of the fibrewise functionals -/

/-- The correspondence of the fibrewise functionals of the two line bundles: for a morphism
`h : W ⟶ Y'` of a test scheme to the new base, a morphism of `𝒪_{Y'}`-modules
`(g^*M)^{⊗ -1} ⟶ h_* 𝒪_W` is the same thing as a morphism of `𝒪_Y`-modules
`M^{⊗ -1} ⟶ (h ≫ g)_* 𝒪_W`: the base change of the inverse followed by the generic
transposition `Stacks.LineBundle.Situation.transposeEquiv`. -/
def pushforwardTransposeEquiv {W : Scheme.{u}} (h : W ⟶ Y') :
    ((inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L ⟶
        (Scheme.Modules.pushforward h).obj (SheafOfModules.unit W.ringCatSheaf)) ≃
      ((inverseSituation Y M).L ⟶
        (Scheme.Modules.pushforward (h ≫ g)).obj (SheafOfModules.unit W.ringCatSheaf)) :=
  (Iso.homFromEquiv (inverseSituationPullbackIso g M).symm).trans
    ((inverseSituation Y M).transposeEquiv g h)

/-- The transposition of fibrewise functionals, written out: compose with the base change of the
inverse, transpose across the pullback--pushforward adjunction, and identify the two composite
direct images. -/
theorem pushforwardTransposeEquiv_apply {W : Scheme.{u}} (h : W ⟶ Y')
    (φ : (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L ⟶
      (Scheme.Modules.pushforward h).obj (SheafOfModules.unit W.ringCatSheaf)) :
    pushforwardTransposeEquiv g M h φ =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
          ((inverseSituationPullbackIso g M).hom ≫ φ) ≫
        (Scheme.Modules.pushforwardComp h g).hom.app (SheafOfModules.unit W.ringCatSheaf) :=
  rfl

/-- The base change on pairs: the point of `L(M)` over `h ≫ g` attached to a point of `L(M')`
over `h`, read as a pair in the functor of points. -/
def pairBaseChange {W : Scheme.{u}}
    (p : Σ k : W ⟶ Y', ((inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L ⟶
      (Scheme.Modules.pushforward k).obj (SheafOfModules.unit W.ringCatSheaf))) :
    Σ k : W ⟶ Y, ((inverseSituation Y M).L ⟶
      (Scheme.Modules.pushforward k).obj (SheafOfModules.unit W.ringCatSheaf)) :=
  ⟨p.1 ≫ g, pushforwardTransposeEquiv g M p.1 p.2⟩

/-- The generic base change on pairs, read through the base change of the inverse, is the base
change on pairs of the two line bundles. -/
theorem baseChangePoint_eq_pairBaseChange {W : Scheme.{u}}
    (p : Σ k : W ⟶ Y', ((inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L ⟶
      (Scheme.Modules.pushforward k).obj (SheafOfModules.unit W.ringCatSheaf))) :
    (inverseSituation Y M).baseChangePoint g
        ⟨p.1, (inverseSituationPullbackIso g M).hom ≫ p.2⟩ =
      pairBaseChange g M p :=
  rfl

/-! ### The canonical morphism of total spaces -/

/-- The canonical morphism `β : L(M') ⟶ L(M)` from the line bundle of the pulled-back module to
the line bundle of the original one: the identification of `L(M')` with the total space of the
base-changed situation, followed by the canonical morphism of that base change. -/
def totalSpaceBaseChange :
    lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M) ⟶ lineBundleSpace Y M :=
  (inverseSituationBaseChangeIso g M).hom ≫ (inverseSituation Y M).baseChangeToTotalSpace g

/-- The canonical morphism, factored into its two legs. -/
theorem totalSpaceBaseChange_eq :
    totalSpaceBaseChange g M =
      (inverseSituationBaseChangeIso g M).hom ≫
        (inverseSituation Y M).baseChangeToTotalSpace g :=
  rfl

/-- The canonical morphism of total spaces lies over `g`: `β ≫ q = q' ≫ g`. -/
theorem totalSpaceBaseChange_comp_lineBundleProj :
    totalSpaceBaseChange g M ≫ lineBundleProj Y M =
      lineBundleProj Y' ((Scheme.Modules.pullback g).obj M) ≫ g := by
  have := congrArg (· ≫ g) (inverseSituationBaseChangeIso_hom_comp_totalSpaceToBase g M)
  erw [totalSpaceBaseChange, Category.assoc,
    (inverseSituation Y M).baseChangeToTotalSpace_comp_totalSpaceToBase g, ← Category.assoc]
  exact this

/-- Composing a point of `L(M')` with the canonical morphism transposes that point. -/
theorem totalSpaceHomEquiv_comp_totalSpaceBaseChange {W : Scheme.{u}}
    (m : W ⟶ lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M)) :
    (inverseSituation Y M).totalSpaceHomEquiv W (m ≫ totalSpaceBaseChange g M) =
      pairBaseChange g M
        ((inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).totalSpaceHomEquiv W m) := by
  have := isInvertible_baseChange_inverse g M
  have hstep : ((inverseSituation Y M).baseChange g).totalSpaceHomEquiv W
        (m ≫ (inverseSituationBaseChangeIso g M).hom) =
      ⟨((inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).totalSpaceHomEquiv W m).1,
        (inverseSituationPullbackIso g M).hom ≫
          ((inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).totalSpaceHomEquiv
            W m).2⟩ :=
    Eq.trans
      (congrArg (((inverseSituation Y M).baseChange g).totalSpaceHomEquiv W)
        (((inverseSituation Y M).baseChange g).comp_totalSpaceMapOfIso
          (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L
          (inverseSituationPullbackIso g M) m))
      (((inverseSituation Y M).baseChange g).totalSpaceHomEquiv_totalSpaceHomEquivCongr
        (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L
        (inverseSituationPullbackIso g M) m)
  refine Eq.trans (congrArg ((inverseSituation Y M).totalSpaceHomEquiv W)
    (Category.assoc m (inverseSituationBaseChangeIso g M).hom
      ((inverseSituation Y M).baseChangeToTotalSpace g)).symm) ?_
  refine Eq.trans ((inverseSituation Y M).totalSpaceHomEquiv_comp_baseChangeToTotalSpace g
    (m ≫ (inverseSituationBaseChangeIso g M).hom)) ?_
  exact Eq.trans (congrArg ((inverseSituation Y M).baseChangePoint g) hstep)
    (baseChangePoint_eq_pairBaseChange g M _)

/-- The identification of the two total spaces, read backwards, is one of schemes over `Y'`. -/
theorem inverseSituationBaseChangeIso_inv_comp_lineBundleProj :
    (inverseSituationBaseChangeIso g M).inv ≫
        lineBundleProj Y' ((Scheme.Modules.pullback g).obj M) =
      ((inverseSituation Y M).baseChange g).totalSpaceToBase :=
  (Iso.inv_comp_eq _).mpr
    (inverseSituationBaseChangeIso_hom_comp_totalSpaceToBase g M).symm

/-- A point of `L(M)` and a point of `Y'` agreeing over `Y` lift uniquely to a point of
`L(g^*M)`. -/
theorem existsUnique_lift_totalSpaceBaseChange {W : Scheme.{u}}
    (b : W ⟶ lineBundleSpace Y M) (a : W ⟶ Y')
    (hab : b ≫ lineBundleProj Y M = a ≫ g) :
    ∃! m : W ⟶ lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M),
      m ≫ totalSpaceBaseChange g M = b ∧
        m ≫ lineBundleProj Y' ((Scheme.Modules.pullback g).obj M) = a := by
  have hP : IsPullback ((inverseSituation Y M).baseChangeToTotalSpace g)
      ((inverseSituation Y M).baseChange g).totalSpaceToBase
      (inverseSituation Y M).totalSpaceToBase g :=
    (inverseSituation Y M).isPullback_baseChange g
  refine ⟨hP.lift b a hab ≫ (inverseSituationBaseChangeIso g M).inv, ⟨?_, ?_⟩, ?_⟩
  · exact (Category.assoc _ _ _).trans
      ((congrArg (hP.lift b a hab ≫ ·) (Iso.inv_hom_id_assoc _ _)).trans (hP.lift_fst b a hab))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (hP.lift b a hab ≫ ·)
          (inverseSituationBaseChangeIso_inv_comp_lineBundleProj g M)).trans
        (hP.lift_snd b a hab))
  · rintro m ⟨hm₁, hm₂⟩
    rw [Iso.eq_comp_inv]
    refine hP.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans (hm₁.trans (hP.lift_fst b a hab).symm)
    · exact (Category.assoc _ _ _).trans
        ((congrArg (m ≫ ·) (inverseSituationBaseChangeIso_hom_comp_totalSpaceToBase g M)).trans
          (hm₂.trans (hP.lift_snd b a hab).symm))

/-- The total space of a line bundle commutes with arbitrary base change: the square with
sides `L(g^*M) ⟶ L(M)`, `L(g^*M) ⟶ Y'`, `L(M) ⟶ Y` and `g : Y' ⟶ Y` is cartesian, with no
hypothesis on `g`, `Y` or `Y'`. -/
theorem isPullback_totalSpaceBaseChange :
    IsPullback (totalSpaceBaseChange g M)
      (lineBundleProj Y' ((Scheme.Modules.pullback g).obj M)) (lineBundleProj Y M) g :=
  IsPullback.of_isLimit' ⟨totalSpaceBaseChange_comp_lineBundleProj g M⟩
    (PullbackCone.IsLimit.mk (totalSpaceBaseChange_comp_lineBundleProj g M)
      (fun s => (existsUnique_lift_totalSpaceBaseChange g M s.fst s.snd s.condition).choose)
      (fun s =>
        (existsUnique_lift_totalSpaceBaseChange g M s.fst s.snd s.condition).choose_spec.1.1)
      (fun s =>
        (existsUnique_lift_totalSpaceBaseChange g M s.fst s.snd s.condition).choose_spec.1.2)
      (fun s m h1 h2 =>
        (existsUnique_lift_totalSpaceBaseChange g M s.fst s.snd
          s.condition).choose_spec.2 m ⟨h1, h2⟩))

/-! ### The fibre-coordinate datum under base change -/

/-- The fibre-coordinate datum commutes with base change: the degree-one inclusion
`M^{⊗ -1} ⟶ q_* 𝒪_{L(M)}` (whose adjoint is the tautological functional), pushed along the
canonical morphism `β : L(M') ⟶ L(M)`, is the transposition across the base change of the
degree-one inclusion `(g^*M)^{⊗ -1} ⟶ q'_* 𝒪_{L(M')}` of the line bundle of `g^*M`. Both sides
are read as pairs in the functor of points of `L(M)`. -/
theorem totalSpaceHomEquiv_totalSpaceBaseChange :
    (⟨totalSpaceBaseChange g M ≫ lineBundleProj Y M,
        (inverseSituation Y M).genToPushforward ≫
          structureComparison (lineBundleProj Y M) (totalSpaceBaseChange g M)⟩ :
      Σ k : lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M) ⟶ Y,
        ((inverseSituation Y M).L ⟶ (Scheme.Modules.pushforward k).obj
          (SheafOfModules.unit
            (lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M)).ringCatSheaf))) =
      ⟨lineBundleProj Y' ((Scheme.Modules.pullback g).obj M) ≫ g,
        pushforwardTransposeEquiv g M (lineBundleProj Y' ((Scheme.Modules.pullback g).obj M))
          (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).genToPushforward⟩ := by
  have h1 : (inverseSituation Y M).totalSpaceHomEquiv
        (lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M)) (totalSpaceBaseChange g M) =
      pairBaseChange g M
        ((inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).totalSpaceHomEquiv
          (lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M)) (𝟙 _)) :=
    Eq.trans
      (congrArg
        ((inverseSituation Y M).totalSpaceHomEquiv
          (lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M)))
        (Category.id_comp (totalSpaceBaseChange g M)).symm)
      (totalSpaceHomEquiv_comp_totalSpaceBaseChange g M
        (𝟙 (lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M))))
  refine Eq.trans (sigma_mk_congr
    ((inverseSituation Y M).totalSpaceHomEquiv_snd (totalSpaceBaseChange g M))).symm ?_
  exact Eq.trans h1 (congrArg (pairBaseChange g M) (sigma_mk_congr
    (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).totalSpaceHomEquiv_id))

end Stacks.LineBundle

end
