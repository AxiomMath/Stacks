module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionSteinCase
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ExceptionalCurveLocus
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleFiniteDescent.Basic
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
import all StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk

/-!
# The classifying morphism of a blowup at a regular point is an isomorphism

Let `z` be a closed point of a Noetherian scheme `Y` whose local ring is regular of dimension two,
and let `g : X ⟶ Bl_z Y` be a morphism over a proper `f : X ⟶ Y`. This file gives a criterion for
`g` to be an isomorphism, based on item (4) of [Stacks, Tag 0BFP], and the resulting existence
statement for contractions of exceptional curves of the first kind ([Stacks, Tag 0C2L]).

## Main results

* `AlgebraicGeometry.isNormalRing_stalk_blowUp_of_mapsTo`: the local rings of the blowup of a
  regular closed point of dimension two are normal at every point over the centre.
* `AlgebraicGeometry.isIso_of_isBirational_of_forall_isNormal_quasiFiniteAt`: a proper
  birational morphism with reduced source onto a Noetherian scheme is an isomorphism as soon as
  every point of the target either lies in an open over which the morphism restricts to an
  isomorphism, or has a normal local ring together with a preimage at which the morphism is
  quasi-finite.
* `AlgebraicGeometry.isIso_of_comp_blowUpToBase_eq_of_isBirational`: a birational morphism
  `g : X ⟶ Bl_z Y` over a proper `f : X ⟶ Y`, with `X` reduced, is an isomorphism as soon as it is
  quasi-finite somewhere over each point of the exceptional curve of `Bl_z Y` and is an
  isomorphism locally over every point off that curve.
* `AlgebraicGeometry.isIso_of_comp_blowUpToBase_eq_of_isBirational_of_isIntegral`: the same on
  integral schemes, with birationality asked of `f` instead of `g`.
* `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isBirational_blowUpClassifying`:
  a contraction of an exceptional curve of the first kind exists under the hypotheses of
  [Stacks, Tag 0C2L] together with the inputs of the criterion above.

## References

* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The local rings of the blowup of a regular closed point of dimension two are normal at
every point lying over the centre. -/
public theorem isNormalRing_stalk_blowUp_of_mapsTo {X : Scheme.{u}} (I : X.IdealSheafData)
    (z : X) (hz : IsClosed ({z} : Set X))
    (hI : I = Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X))
    (hreg : IsRegularLocalRing (X.presheaf.stalk z))
    (hdim : ringKrullDim (X.presheaf.stalk z) = 2)
    (y : AlgebraicGeometry.blowUp I) (hy : AlgebraicGeometry.blowUpToBase I y = z) :
    IsNormalRing ((AlgebraicGeometry.blowUp I).presheaf.stalk y) :=
  have : IsRegularLocalRing ((AlgebraicGeometry.blowUp I).presheaf.stalk y) :=
    isRegularLocalRing_stalk_blowUp_of_mapsTo I z hz hI hreg hdim y hy
  have := IsRegularLocalRing.isDomain ((AlgebraicGeometry.blowUp I).presheaf.stalk y)
  have := isIntegrallyClosed_of_isRegularLocalRing
    ((AlgebraicGeometry.blowUp I).presheaf.stalk y)
  IsNormalRing.of_isIntegrallyClosed _

/-- Let `f : X ⟶ Y` be a proper birational morphism with `X` reduced and `Y` Noetherian. Suppose
every point `y` of `Y` either lies in an open over which `f` restricts to an isomorphism, or has a
normal local ring together with a preimage at which `f` is quasi-finite. Then `f` is an
isomorphism. -/
public theorem isIso_of_isBirational_of_forall_isNormal_quasiFiniteAt {X Y : Scheme.{u}}
    [IsNoetherian Y] [IsReduced X] (f : X ⟶ Y) [IsProper f] (hf : IsBirational f)
    (h : ∀ y : Y, (∃ V : Y.Opens, y ∈ V ∧ IsIso (f ∣_ V)) ∨
      (IsNormalRing (Y.presheaf.stalk y) ∧ ∃ x : X, f.base x = y ∧ quasiFiniteAt f x)) :
    IsIso f := by
  obtain ⟨U, hU⟩ := Stacks.ResolutionOfSurfaces.exists_maximal_isomorphism_open f
  have hmem : ∀ y : Y, y ∈ U := by
    intro y
    rcases h y with hres | ⟨hnormal, x, hx, hqf⟩
    · exact mem_maximal_isomorphism_open_of_exists_isIso_restrict f U hU y hres
    · exact mem_maximal_isomorphism_open_of_quasiFiniteAt_of_isNormal f hf U hU y hnormal x hx
        hqf
  have hUtop : U = ⊤ := TopologicalSpace.Opens.ext (Set.eq_univ_iff_forall.mpr hmem)
  have : IsIso (f ∣_ (⊤ : Y.Opens)) := hUtop ▸ hU.1
  exact Stacks.AlgebraicGeometry.InvertibleFiniteDescent.isIso_of_isIso_morphismRestrict_top f

/-- Let `z` be a closed point of a Noetherian scheme `Y` whose local ring is regular of dimension
two, `f : X ⟶ Y` proper with `X` reduced, and `g : X ⟶ Bl_z Y` birational with `g` followed by
the blowup morphism equal to `f`. If `g` is quasi-finite somewhere over each point of the
exceptional curve and is locally an isomorphism over every point off that curve, then `g` is an
isomorphism. -/
public theorem isIso_of_comp_blowUpToBase_eq_of_isBirational {X Y : Scheme.{u}} [IsNoetherian Y]
    [IsReduced X] (I : Y.IdealSheafData) (z : Y) (hz : IsClosed ({z} : Set Y))
    (hI : I = Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Y))
    (hreg : IsRegularLocalRing (Y.presheaf.stalk z))
    (hdim : ringKrullDim (Y.presheaf.stalk z) = 2) (f : X ⟶ Y) [IsProper f]
    (g : X ⟶ AlgebraicGeometry.blowUp I)
    (hg : g ≫ AlgebraicGeometry.blowUpToBase I = f) (hbir : IsBirational g)
    (hqf : ∀ w : AlgebraicGeometry.blowUp I, AlgebraicGeometry.blowUpToBase I w = z →
      ∃ x : X, g.base x = w ∧ g.QuasiFiniteAt x)
    (hres : ∀ w : AlgebraicGeometry.blowUp I, AlgebraicGeometry.blowUpToBase I w ≠ z →
      ∃ V : (AlgebraicGeometry.blowUp I).Opens, w ∈ V ∧ IsIso (g ∣_ V)) :
    IsIso g := by
  have : IsNoetherian (AlgebraicGeometry.blowUp I) :=
    Stacks.ResolutionOfSurfaces.isNoetherian_blowUp I
  have : IsSeparated (AlgebraicGeometry.blowUpToBase I) :=
    Stacks.RelativeProj.Situation.isSeparated_relativeProjToBase _
  have hproper : IsProper g :=
    isProper_of_isProper_of_isSeparated g (AlgebraicGeometry.blowUpToBase I) f hg
  refine isIso_of_isBirational_of_forall_isNormal_quasiFiniteAt g hbir fun w ↦ ?_
  by_cases hw : AlgebraicGeometry.blowUpToBase I w = z
  · obtain ⟨x, hx, hqfx⟩ := hqf w hw
    exact Or.inr ⟨isNormalRing_stalk_blowUp_of_mapsTo I z hz hI hreg hdim w hw, x, hx,
      finiteTypeAt_of_locallyOfFiniteType g x, hqfx⟩
  · exact Or.inl (hres w hw)

/-- The variant of `AlgebraicGeometry.isIso_of_comp_blowUpToBase_eq_of_isBirational` for integral
`X` and `Y` and a nonzero centre, with birationality asked of `f` rather than of `g`. -/
public theorem isIso_of_comp_blowUpToBase_eq_of_isBirational_of_isIntegral {X Y : Scheme.{u}}
    [IsNoetherian Y] [IsIntegral X] [IsIntegral Y] (I : Y.IdealSheafData) (hI0 : I ≠ ⊥) (z : Y)
    (hz : IsClosed ({z} : Set Y))
    (hI : I = Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Y))
    (hreg : IsRegularLocalRing (Y.presheaf.stalk z))
    (hdim : ringKrullDim (Y.presheaf.stalk z) = 2) (f : X ⟶ Y) [IsProper f]
    (hbir : IsBirational f) (g : X ⟶ AlgebraicGeometry.blowUp I)
    (hg : g ≫ AlgebraicGeometry.blowUpToBase I = f)
    (hqf : ∀ w : AlgebraicGeometry.blowUp I, AlgebraicGeometry.blowUpToBase I w = z →
      ∃ x : X, g.base x = w ∧ g.QuasiFiniteAt x)
    (hres : ∀ w : AlgebraicGeometry.blowUp I, AlgebraicGeometry.blowUpToBase I w ≠ z →
      ∃ V : (AlgebraicGeometry.blowUp I).Opens, w ∈ V ∧ IsIso (g ∣_ V)) :
    IsIso g :=
  isIso_of_comp_blowUpToBase_eq_of_isBirational I z hz hI hreg hdim f g hg
    (isBirational_of_comp_blowUpToBase I hI0 g (by rw [hg]; exact hbir)) hqf hres

/-- A contraction of an exceptional curve of the first kind exists, under the hypotheses of
[Stacks, Tag 0C2L] on `f` together with `hreg`, `hdim` and `hfibre`, provided `X` and `Y` are
integral with the centre nonzero, `f` is birational, and every classifying morphism into the
blowup is quasi-finite somewhere over each point of the exceptional curve and locally an
isomorphism over every point off that curve. -/
public theorem exists_isContractionOfExceptionalCurve_of_isBirational_blowUpClassifying
    {X Y : Scheme.{u}} [IsNoetherian Y] [IsIntegral X] [IsIntegral Y] {D : X.IdealSheafData}
    {k : Type u} [Field k] {e : projectiveLineProj k ≅ D.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (f : X ⟶ Y) [IsProper f] (hbir : IsBirational f) (y : Y)
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2)
    (hfibre : ∀ hy : IsClosed ({y} : Set Y),
      D = (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap f)
    (hI0 : ∀ hy : IsClosed ({y} : Set Y),
      Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ≠ ⊥)
    (hqf : ∀ (hy : IsClosed ({y} : Set Y)) (g : X ⟶ AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))),
      g ≫ AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f →
      ∀ w : AlgebraicGeometry.blowUp
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)),
        AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) w = y →
        ∃ x : X, g.base x = w ∧ g.QuasiFiniteAt x)
    (hres : ∀ (hy : IsClosed ({y} : Set Y)) (g : X ⟶ AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))),
      g ≫ AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f →
      ∀ w : AlgebraicGeometry.blowUp
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)),
        AlgebraicGeometry.blowUpToBase
            (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) w ≠ y →
        ∃ V : (AlgebraicGeometry.blowUp
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))).Opens,
          w ∈ V ∧ IsIso (g ∣_ V)) :
    ∃ (Z : Scheme.{u}) (b : X ⟶ Z), IsContractionOfExceptionalCurve D b :=
  exists_isContractionOfExceptionalCurve_of_isProper_of_isIso_blowUpClassifying hE f y hmaps
    hreg hdim hfibre fun hy g hgf ↦
      isIso_of_comp_blowUpToBase_eq_of_isBirational_of_isIntegral _ (hI0 hy) y hy rfl hreg hdim
        f hbir g hgf (hqf hy g hgf) (hres hy g hgf)

end AlgebraicGeometry

end
