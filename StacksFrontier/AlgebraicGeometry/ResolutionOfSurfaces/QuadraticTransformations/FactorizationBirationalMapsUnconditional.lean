module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMaps
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMaps
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalSurfaces
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Factorization of birational maps, without the blowup-surface hypothesis

The declarations of `FactorizationBirationalMaps` take as an explicit `blowUpSurface` hypothesis
the proposition that the blowup of an integral Noetherian scheme regular of dimension two at a
closed point is again such a scheme. That proposition is proved here,
`Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_blowUp_vanishingIdeal_singleton`, from the
globalization of [Stacks, Tag 0AGR], and the results are restated without it.

## Main results

* `Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_blowUp_vanishingIdeal_singleton`: the
  blowup at a closed point of an integral Noetherian scheme regular of dimension two is again such
  a scheme.
* `Stacks.ResolutionOfSurfaces.birationalOver_comp_of_factorsAsPointBlowups_unconditional`: a
  finite sequence of blowups at closed points makes its source birational to the target over any
  base.
* `Stacks.ResolutionOfSurfaces.birationalOver_of_exists_factorsAsPointBlowups`: the converse
  direction of [Stacks, Tag 0C5S], whose proof the source omits, proved outright.
* `Stacks.ResolutionOfSurfaces.exists_factorsAsPointBlowups_of_birationalOver_unconditional` and
  `Stacks.ResolutionOfSurfaces.birationalOver_iff_exists_factorsAsPointBlowups_unconditional`: the
  forward direction and the two directions combined, which still take `descent`, `reduction` and
  `h0C5R` as hypotheses and so carry no registration.

## References

* [Stacks Project, Tag 0C5S](https://stacks.math.columbia.edu/tag/0C5S)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### The blowup at a closed point of a surface is a surface -/

/-- **The blowup at a closed point of an integral Noetherian scheme regular of dimension two is
again such a scheme.** Integrality and Noetherianity are
`Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_pointBlowUp`; regularity and the dimension
are the globalization of [Stacks, Tag 0AGR],
`AlgebraicGeometry.isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton`.

This is the proposition that the declarations below used to take as an explicit `blowUpSurface`
argument, on the strength of a module docstring saying the library had [Stacks, Tag 0AGR] only
for the blowup of `Spec A` at the closed point of a two-dimensional regular local ring. That
reading was out of date. -/
@[ega "IV 19.4.11" "(iii), special case"]
public theorem isIntegralRegularSurface_blowUp_vanishingIdeal_singleton (A : Scheme.{u}) (a : A)
    (ha : IsClosed ({a} : Set A)) (hA : IsIntegralRegularSurface A) :
    IsIntegralRegularSurface
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))) :=
  have := hA.isNoetherian
  have h := isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton A hA.isRegular
    hA.topologicalKrullDim_eq a ha
  isIntegralRegularSurface_pointBlowUp hA ha h.1 h.2

/-- The source of a chain of blowups at closed points of an integral Noetherian scheme regular of
dimension two is again such a scheme, and the composite morphism is proper. -/
public theorem isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional
    {X Z : Scheme.{u}} {T : Set X} {p : Z ⟶ X} (hp : PointBlowupChain X T Z p)
    (hX : IsIntegralRegularSurface X) : IsIntegralRegularSurface Z ∧ IsProper p := by
  induction hp with
  | refl => exact ⟨hX, inferInstance⟩
  | step hh w hw hwT ih =>
    obtain ⟨hWsurface, hWproper⟩ := ih
    have hWnoetherian := hWsurface.isNoetherian
    refine ⟨isIntegralRegularSurface_blowUp_vanishingIdeal_singleton _ w hw hWsurface, ?_⟩
    have hblow : IsProper (blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds _))) := inferInstance
    exact MorphismProperty.comp_mem _ _ _ hblow hWproper

/-- A chain of blowups at closed points of an integral Noetherian scheme regular of dimension two
makes its source birational to the target over any base. -/
public theorem birationalOver_comp_of_pointBlowupChain_unconditional
    {S X Z : Scheme.{u}} (sX : X ⟶ S) {T : Set X} {p : Z ⟶ X}
    (hp : PointBlowupChain X T Z p) (hX : IsIntegralRegularSurface X) :
    Scheme.BirationalOver (p ≫ sX) sX := by
  induction hp with
  | refl => simpa using Scheme.BirationalOver.refl sX
  | step hh w hw hwT ih =>
    rw [Category.assoc]
    exact (birationalOver_blowUpToBase
      (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hh hX).1
      w hw _).trans ih

/-- **One side of the converse direction of [Stacks, Tag 0C5S], whose proof the source omits.** A
morphism which is a finite sequence of blowups at closed points of an integral Noetherian scheme
regular of dimension two makes its source birational to the target over any base. -/
@[stacks 0C5S "one side of the converse direction, which the source states without proof: a
chain of blowups in closed points out of `X` makes its source birational to `X` over the base.
The route is Tag 02OS, nonvanishing of the point's ideal sheaf, and Tag 0BAD, and the blowup of
such a scheme at a closed point is again such a scheme by the globalization of Tag 0AGR,
`AlgebraicGeometry.isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton`"]
public theorem birationalOver_comp_of_factorsAsPointBlowups_unconditional
    {S X Z : Scheme.{u}} (sX : X ⟶ S) (hX : IsIntegralRegularSurface X) {f : Z ⟶ X}
    (hf : FactorsAsPointBlowups X Set.univ Z f) :
    Scheme.BirationalOver (f ≫ sX) sX := by
  obtain ⟨W, q, hchain, e, rfl⟩ := hf
  rw [Category.assoc]
  exact (e.hom.birationalOver (q ≫ sX) (e.hom ≫ q ≫ sX) rfl).trans
    (birationalOver_comp_of_pointBlowupChain_unconditional sX hchain hX)

/-- **The converse direction of [Stacks, Tag 0C5S], whose proof the source omits.** Let `S` be a
Noetherian scheme and let `X` and `Y` be proper integral schemes over `S` which are regular of
dimension two. If there is a scheme `Z` with `S`-morphisms `f : Z ⟶ X` and `g : Z ⟶ Y`, each a
finite sequence of blowups at closed points, then `X` and `Y` are `S`-birational.

This is the implication of the source's `if and only if` that the source states without proof,
and it is proved here with nothing assumed: each of the two sides makes `Z` birational to its
target over `S` by
`Stacks.ResolutionOfSurfaces.birationalOver_comp_of_factorsAsPointBlowups_unconditional`,
and `S`-birationality is symmetric and transitive. -/
@[stacks 0C5S "the implication from the two-sided chain of blowups in closed points to
`S`-birationality of `X` and `Y`, which is the direction the source states without proof. Nothing
is assumed: the two sides are composed through
`Stacks.ResolutionOfSurfaces.birationalOver_comp_of_factorsAsPointBlowups_unconditional` and the
symmetry and transitivity of `AlgebraicGeometry.Scheme.BirationalOver`"]
public theorem birationalOver_of_exists_factorsAsPointBlowups
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    (hX : IsIntegralRegularSurface X) (hY : IsIntegralRegularSurface Y)
    (h : ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
      f ≫ (X ↘ S) = g ≫ (Y ↘ S) ∧
        FactorsAsPointBlowups X Set.univ Z f ∧ FactorsAsPointBlowups Y Set.univ Z g) :
    Scheme.BirationalOver (X ↘ S) (Y ↘ S) := by
  obtain ⟨Z, f, g, hfg, hf, hg⟩ := h
  have hgY : Scheme.BirationalOver (f ≫ (X ↘ S)) (Y ↘ S) := by
    rw [hfg]
    exact birationalOver_comp_of_factorsAsPointBlowups_unconditional (Y ↘ S) hY hg
  exact (birationalOver_comp_of_factorsAsPointBlowups_unconditional (X ↘ S) hX hf).symm.trans
    hgY

/-- **The forward direction of [Stacks, Tag 0C5S].** Let `S` be a Noetherian scheme and let `X`
and `Y` be proper integral schemes over `S` which are regular of dimension two. If `X` and `Y`
are `S`-birational then there is a scheme `Z` with `S`-morphisms `f : Z ⟶ X` and `g : Z ⟶ Y`,
each a finite sequence of blowups at closed points.

Three inputs are carried as hypotheses: `descent`, the local splitting of [Stacks, Tag 0AGT], and
`reduction`, the enlargement of the domain of an `S`-rational map resting on
[Stacks, Tag 0BX7] and [Stacks, Tag 081T], which are what the library's form of
[Stacks, Tag 0C5H] consumes; and `h0C5R`, which is [Stacks, Tag 0C5R]. -/
public theorem exists_factorsAsPointBlowups_of_birationalOver_unconditional
    (descent : PointBlowupColengthDescent.{u})
    (h0C5R : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g →
        FactorsAsPointBlowups A Set.univ B g)
    {S X Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] [X.Over S] [Y.Over S]
    [IsProper (X ↘ S)] [IsProper (Y ↘ S)]
    (reduction : ∀ f : X.PartialMap Y, f.IsOver S →
      ∃ (T : Finset X) (V : X.Opens) (hle : f.domain ≤ V) (g : (V : Scheme.{u}) ⟶ Y),
        (V : Set X) = (T : Set X)ᶜ ∧
        (∀ x ∈ T, IsClosed ({x} : Set X)) ∧
        (∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2) ∧
        g ≫ (Y ↘ S) = V.ι ≫ (X ↘ S) ∧
        X.homOfLE hle ≫ g = f.hom ∧
        ∀ {B : Scheme.{u}} (q : B ⟶ X) [IsProper q] [IsIso (q ∣_ V)],
          ∃ (A' : Scheme.{u}) (b : A' ⟶ X), Stacks.Blowup.IsAdmissibleBlowup V b ∧
            ∃ h : A' ⟶ B, h ≫ q = b)
    (hX : IsIntegralRegularSurface X) (hY : IsIntegralRegularSurface Y)
    (hbirational : Scheme.BirationalOver (X ↘ S) (Y ↘ S)) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
      f ≫ (X ↘ S) = g ≫ (Y ↘ S) ∧
        FactorsAsPointBlowups X Set.univ Z f ∧ FactorsAsPointBlowups Y Set.univ Z g := by
  have hXint := hX.isIntegral
  have hYint := hY.isIntegral
  have hXnoetherian := hX.isNoetherian
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := by
    have hstalks : IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
      ((isRegular_tfae X).out 1 2).mp hX.isRegular
    exact hstalks.2
  set pIso := hbirational.partialIso (X ↘ S) (Y ↘ S)
  have hpmOver : pIso.toPartialMap.IsOver S := by
    refine ⟨?_⟩
    change (pIso.iso.hom ≫ pIso.target.ι) ≫ (Y ↘ S) = pIso.source.ι ≫ (X ↘ S)
    rw [Category.assoc]
    exact hbirational.partialIso_isOver (X ↘ S) (Y ↘ S)
  obtain ⟨Z, p, q, hchain, hqS, hagree⟩ :=
    exists_pointBlowupChain_resolving_partialMap descent
      domination_of_exists_pointBlowupChain_factorization hreg
      pIso.toPartialMap (reduction pIso.toPartialMap hpmOver)
  obtain ⟨hZsurface, hZproper⟩ :=
    isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hchain hX
  have hZint := hZsurface.isIntegral
  have hpbirational : IsBirational p :=
    isBirational_of_birationalOver_id p
      (by simpa using birationalOver_comp_of_pointBlowupChain_unconditional (𝟙 X) hchain hX)
  have hqbirational : IsBirational q :=
    isBirational_of_resolves_partialIso pIso p q hpbirational hagree
  have hqproper : IsProper q := by
    have hcomp : IsProper (p ≫ (X ↘ S)) := inferInstance
    rw [← hqS] at hcomp
    exact IsProper.of_comp q (Y ↘ S)
  exact ⟨Z, p, q, hqS.symm,
    ⟨Z, p, pointBlowupChain_univ hchain, Iso.refl Z, by simp⟩,
    h0C5R Y Z q hY hZsurface hqproper hqbirational⟩

/-- The two directions of [Stacks, Tag 0C5S] combined. Let `S` be a Noetherian scheme and let `X`
and `Y` be proper integral schemes over `S` which are regular of dimension two. Then `X` and `Y`
are `S`-birational if and only if there is a scheme `Z` with `S`-morphisms `f : Z ⟶ X` and
`g : Z ⟶ Y`, each a finite sequence of blowups at closed points — the diagram
`X = X₀ ← … ← Xₙ = Y_m → … → Y₀ = Y` of the source.

**No `@[stacks 0C5S]` attribute is placed on this declaration.** Its forward direction still
takes three inputs as explicit hypotheses, each of which is an absent Stacks tag rather than a
step of the source's argument: `descent`, the local splitting of [Stacks, Tag 0AGT];
`reduction`, the enlargement of the domain of an `S`-rational map resting on
[Stacks, Tag 0BX7] and [Stacks, Tag 081T] (these two are what the library's form of
[Stacks, Tag 0C5H], `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap`,
itself consumes); and `h0C5R`, which is [Stacks, Tag 0C5R] in full. A declaration proved only
under an assumed input does not formalize its tag, so the registration is carried instead by the
direction that *is* proved outright,
`Stacks.ResolutionOfSurfaces.birationalOver_of_exists_factorsAsPointBlowups`, and by
`Stacks.ResolutionOfSurfaces.birationalOver_comp_of_factorsAsPointBlowups`.

The regularity of the blowup of a regular surface at a closed point is discharged by
`Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_blowUp_vanishingIdeal_singleton`. -/
public theorem birationalOver_iff_exists_factorsAsPointBlowups_unconditional
    (descent : PointBlowupColengthDescent.{u})
    (h0C5R : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g →
        FactorsAsPointBlowups A Set.univ B g)
    {S X Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] [X.Over S] [Y.Over S]
    [IsProper (X ↘ S)] [IsProper (Y ↘ S)]
    (reduction : ∀ f : X.PartialMap Y, f.IsOver S →
      ∃ (T : Finset X) (V : X.Opens) (hle : f.domain ≤ V) (g : (V : Scheme.{u}) ⟶ Y),
        (V : Set X) = (T : Set X)ᶜ ∧
        (∀ x ∈ T, IsClosed ({x} : Set X)) ∧
        (∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2) ∧
        g ≫ (Y ↘ S) = V.ι ≫ (X ↘ S) ∧
        X.homOfLE hle ≫ g = f.hom ∧
        ∀ {B : Scheme.{u}} (q : B ⟶ X) [IsProper q] [IsIso (q ∣_ V)],
          ∃ (A' : Scheme.{u}) (b : A' ⟶ X), Stacks.Blowup.IsAdmissibleBlowup V b ∧
            ∃ h : A' ⟶ B, h ≫ q = b)
    (hX : IsIntegralRegularSurface X) (hY : IsIntegralRegularSurface Y) :
    Scheme.BirationalOver (X ↘ S) (Y ↘ S) ↔
      ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
        f ≫ (X ↘ S) = g ≫ (Y ↘ S) ∧
          FactorsAsPointBlowups X Set.univ Z f ∧ FactorsAsPointBlowups Y Set.univ Z g :=
  ⟨exists_factorsAsPointBlowups_of_birationalOver_unconditional descent h0C5R reduction hX hY,
    birationalOver_of_exists_factorsAsPointBlowups hX hY⟩

/-! ### The forms taking the blowup-surface proposition as a hypothesis

The five declarations below are the forms that take as an explicit `blowUpSurface` hypothesis the
proposition that the blowup of an integral Noetherian scheme regular of dimension two at a closed
point is again such a scheme. That proposition is now proved outright as
`Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_blowUp_vanishingIdeal_singleton`, so each of
these simply discards the hypothesis and appeals to the corresponding `_unconditional` form above;
no proof is duplicated. They are kept for callers written against them. The `@[stacks 0C5S]`
registrations sit on the unconditional forms, which are what actually state the tag's content.
-/

end Stacks.ResolutionOfSurfaces

end
