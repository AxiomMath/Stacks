module

public import StacksFrontier.AlgebraicGeometry.Blowup.Admissible
public import StacksFrontier.AlgebraicGeometry.Divisors.Modification.RationalMap
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain

/-!
# Dominating a rational map by quadratic transformations

Let `S` be a scheme, let `X` be a scheme over `S` whose local rings are regular, and let `Y` be
proper over `S`. An `S`-rational map from `X` to `Y` is defined on a dense open `U ⊆ X`, and the
assertion is that a finite sequence of blowups at closed points not lying over `U`,
`Xₙ → … → X₁ → X₀ = X`, carries an `S`-morphism `Xₙ ⟶ Y` agreeing with the rational map.

The argument is the one in the source. The graph construction replaces `X` by a proper
modification `p : X' ⟶ X` which is an isomorphism over the domain and across which the rational
map becomes a morphism `X' ⟶ Y`; a chain of blowups at closed points dominating `p` then carries
the composite to `Y`, and the agreement over the domain transports along the morphism from the
chain to `X'`.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap` — the argument of
  [Stacks, Tag 0C5H] with three inputs taken as arguments; the tag itself, every input proved, is
  `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap_of_dim_two` in
  `DominateRationalMapDimTwo.lean`.

## Implementation notes

A rational map together with the open set on which it is displayed is
`AlgebraicGeometry.Scheme.PartialMap`, as in
[Stacks, Tag 0C4V](https://stacks.math.columbia.edu/tag/0C4V), and "the morphism and the rational
map agree" is the equality of the two composites out of the pullback `Z ×_X U`, which is the
idiom that tag and `Stacks.ResolutionOfSurfaces.exists_normalizedBlowUpChain_resolving_partialMap`
already use. The sequence of blowups is `Stacks.ResolutionOfSurfaces.PointBlowupChain`, whose set
parameter records where the centres may lie; taking it to be the complement of the domain is
exactly the source's requirement that each centre be a closed point not lying over `U`.

Three inputs are threaded through as explicit hypotheses rather than discharged:

* `descent`, the local splitting of [Stacks, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
  at the level of sheaves of ideals, in the shape that the library's form of
  [Stacks, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH) consumes;
* `domination`, [Stacks, Tag 0AHI](https://stacks.math.columbia.edu/tag/0AHI), a proper morphism
  which is an isomorphism away from finitely many closed points with regular two-dimensional
  local rings is dominated by a chain of blowups at closed points over those points;
* `reduction`, the enlargement of the domain to an open whose complement is a finite set of
  closed points with two-dimensional local rings, which is the first sentence of the source's
  proof and rests on [Stacks, Tag 0BX7](https://stacks.math.columbia.edu/tag/0BX7), bundled with
  the dominating `U`-admissible blowup of
  [Stacks, Tag 081T](https://stacks.math.columbia.edu/tag/081T) for that open.

Everything else — the graph modification, the application of `domination`, and the transport of
the agreement from the enlarged domain back to the original one — is unconditional.

## References

* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Stacks.ResolutionOfSurfaces

/-- Enlarging the set in which the centres of a point blowup chain are allowed to lie. -/
private theorem pointBlowupChain_mono {X Z : Scheme.{u}} {T T' : Set X} (hT : T ⊆ T')
    {p : Z ⟶ X} (hp : PointBlowupChain X T Z p) : PointBlowupChain X T' Z p := by
  induction hp with
  | refl => exact .refl
  | step hh w hw hwT ih => exact ih.step w hw (hT hwT)

/-- A morphism is an isomorphism over an open subset of its target as soon as the second
projection from the pullback along that open subset is an isomorphism. -/
private theorem isIso_morphismRestrict_of_isIso_pullback_snd {A B : Scheme.{u}} (p : A ⟶ B)
    (U : B.Opens) (hiso : IsIso (pullback.snd p U.ι)) : IsIso (p ∣_ U) := by
  have hcomp : IsIso ((pullbackRestrictIsoRestrict p U).hom ≫ p ∣_ U) := by
    rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]
    exact hiso
  exact IsIso.of_isIso_comp_left (pullbackRestrictIsoRestrict p U).hom (p ∣_ U)

/-- The argument of [Stacks, Tag 0C5H], with three of its inputs taken as arguments. Let `S` be a
scheme, let `X` be a Noetherian scheme over `S` all of whose local rings are regular, and let `Y`
be proper over `S`. Given an `S`-rational map from `X` to `Y`, displayed on the dense open
`f.domain`, and the three inputs below, there is a chain of blowups at closed points not lying
over `f.domain`, with composite `p : Z ⟶ X`, and an `S`-morphism `h : Z ⟶ Y` which agrees with
the rational map over `f.domain`.

The inputs are `descent`, the local splitting of [Stacks, Tag 0AGT] in the shape the library's
[Stacks, Tag 0AHH] consumes; `domination`, [Stacks, Tag 0AHI]; and `reduction`, the source's
reduction to a domain containing every codimension-one point, resting on [Stacks, Tag 0BX7],
bundled with the dominating `U`-admissible blowup of [Stacks, Tag 081T] for the enlarged domain.
All three are proved for a regular Noetherian scheme of dimension two, in
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap_of_dim_two`. -/
public theorem exists_pointBlowupChain_resolving_partialMap
    (descent : ∀ (A : Scheme.{u}) (W : Finset A) (J : A.IdealSheafData),
      (∀ y ∈ W, IsClosed ({y} : Set A)) →
      (∀ y ∈ W, IsRegularLocalRing (A.presheaf.stalk y)) →
      (∀ y ∈ W, ringKrullDim (A.presheaf.stalk y) = 2) →
      (J.support : Set A) ⊆ (W : Set A) →
      ∀ y ∈ (J.support : Set A), ∀ hy : IsClosed ({y} : Set A),
      ∀ M : A.IdealSheafData, M = Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ →
        ∃ (d : ℕ) (W' : Finset (blowUp M)) (J' : (blowUp M).IdealSheafData),
          exceptionalIdeal M ^ d * J' = J.comap (blowUpToBase M) ∧
          (∀ z ∈ W', IsClosed ({z} : Set (blowUp M))) ∧
          (∀ z ∈ W', IsRegularLocalRing ((blowUp M).presheaf.stalk z)) ∧
          (∀ z ∈ W', ringKrullDim ((blowUp M).presheaf.stalk z) = 2) ∧
          (J'.support : Set (blowUp M)) ⊆ (W' : Set (blowUp M)) ∧
          (∀ z ∈ W', (blowUpToBase M).base z ∈ W) ∧
          totalColength J' W' < totalColength J W)
    (domination : ∀ (_descent : ∀ (A : Scheme.{u}) (W : Finset A) (J : A.IdealSheafData),
        (∀ y ∈ W, IsClosed ({y} : Set A)) →
        (∀ y ∈ W, IsRegularLocalRing (A.presheaf.stalk y)) →
        (∀ y ∈ W, ringKrullDim (A.presheaf.stalk y) = 2) →
        (J.support : Set A) ⊆ (W : Set A) →
        ∀ y ∈ (J.support : Set A), ∀ hy : IsClosed ({y} : Set A),
        ∀ M : A.IdealSheafData, M = Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ →
          ∃ (d : ℕ) (W' : Finset (blowUp M)) (J' : (blowUp M).IdealSheafData),
            exceptionalIdeal M ^ d * J' = J.comap (blowUpToBase M) ∧
            (∀ z ∈ W', IsClosed ({z} : Set (blowUp M))) ∧
            (∀ z ∈ W', IsRegularLocalRing ((blowUp M).presheaf.stalk z)) ∧
            (∀ z ∈ W', ringKrullDim ((blowUp M).presheaf.stalk z) = 2) ∧
            (J'.support : Set (blowUp M)) ⊆ (W' : Set (blowUp M)) ∧
            (∀ z ∈ W', (blowUpToBase M).base z ∈ W) ∧
            totalColength J' W' < totalColength J W),
      ∀ {A B : Scheme.{u}} [AlgebraicGeometry.IsNoetherian A] (T : Finset A)
      (V : A.Opens), (V : Set A) = (T : Set A)ᶜ →
      (∀ x ∈ T, IsClosed ({x} : Set A)) →
      (∀ x ∈ T, IsRegularLocalRing (A.presheaf.stalk x)) →
      (∀ x ∈ T, ringKrullDim (A.presheaf.stalk x) = 2) →
      ∀ (q : B ⟶ A) [IsProper q] [IsIso (q ∣_ V)],
      (∃ (A' : Scheme.{u}) (b : A' ⟶ A), Stacks.Blowup.IsAdmissibleBlowup V b ∧
          ∃ h : A' ⟶ B, h ≫ q = b) →
        ∃ (Z : Scheme.{u}) (r : Z ⟶ A), PointBlowupChain A (T : Set A) Z r ∧
          ∃ s : Z ⟶ B, s ≫ q = r)
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S] [AlgebraicGeometry.IsNoetherian X]
    [IsProper (Y ↘ S)] (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (f : X.PartialMap Y) [f.IsOver S]
    (reduction : ∃ (T : Finset X) (V : X.Opens) (hle : f.domain ≤ V)
      (g : (V : Scheme.{u}) ⟶ Y),
      (V : Set X) = (T : Set X)ᶜ ∧
      (∀ x ∈ T, IsClosed ({x} : Set X)) ∧
      (∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2) ∧
      g ≫ (Y ↘ S) = V.ι ≫ (X ↘ S) ∧
      X.homOfLE hle ≫ g = f.hom ∧
      ∀ {B : Scheme.{u}} (q : B ⟶ X) [IsProper q] [IsIso (q ∣_ V)],
        ∃ (A' : Scheme.{u}) (b : A' ⟶ X), Stacks.Blowup.IsAdmissibleBlowup V b ∧
          ∃ h : A' ⟶ B, h ≫ q = b) :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ X) (h : Z ⟶ Y),
      PointBlowupChain X ((f.domain : Set X)ᶜ) Z p ∧
        h ≫ (Y ↘ S) = p ≫ (X ↘ S) ∧
          pullback.fst p f.domain.ι ≫ h = pullback.snd p f.domain.ι ≫ f.hom := by
  obtain ⟨T, V, hle, g, hVT, hTclosed, hTdim, hgS, hgf, hadm⟩ := reduction
  have hVdense : Dense (V : Set X) := Dense.mono hle f.dense_domain
  -- The rational map displayed on the enlarged domain `V`.
  let f' : X.PartialMap Y := ⟨V, hVdense, g⟩
  have hf'over : f'.hom.IsOver S := ⟨hgS⟩
  obtain ⟨X', p, f₁, hpproper, hf₁S, hpiso, hpagree⟩ :=
    Stacks.Divisors.exists_proper_modification_resolving_partialMap (S := S) f'
  have hpiso' : IsIso (pullback.snd p V.ι) := hpiso
  have hpagree' : pullback.fst p V.ι ≫ f₁ = pullback.snd p V.ι ≫ g := hpagree
  have hpprop : IsProper p := hpproper
  have hprestrict : IsIso (p ∣_ V) := isIso_morphismRestrict_of_isIso_pullback_snd p V hpiso'
  obtain ⟨Z, r, hchain, s, hs⟩ :=
    domination descent T V hVT hTclosed (fun x _ => hreg x) hTdim p (hadm p)
  -- The centres lie outside `V`, hence outside the original domain.
  have hsub : (T : Set X) ⊆ ((f.domain : Set X))ᶜ := by
    intro x hx hxU
    have hxV : x ∈ (V : Set X) := hle hxU
    rw [hVT] at hxV
    exact hxV hx
  refine ⟨Z, r, s ≫ f₁, pointBlowupChain_mono hsub hchain, ?_, ?_⟩
  · rw [Category.assoc, hf₁S, ← Category.assoc, hs]
  · -- Compare the two morphisms out of `Z ×_X f.domain` through `X' ×_X V`.
    have hcond : (pullback.fst r f.domain.ι ≫ s) ≫ p =
        (pullback.snd r f.domain.ι ≫ X.homOfLE hle) ≫ V.ι := by
      rw [Category.assoc, hs, pullback.condition, Category.assoc, Scheme.homOfLE_ι]
    let m : pullback r f.domain.ι ⟶ pullback p V.ι :=
      pullback.lift (pullback.fst r f.domain.ι ≫ s)
        (pullback.snd r f.domain.ι ≫ X.homOfLE hle) hcond
    have hmfst : m ≫ pullback.fst p V.ι = pullback.fst r f.domain.ι ≫ s :=
      pullback.lift_fst _ _ _
    have hmsnd : m ≫ pullback.snd p V.ι = pullback.snd r f.domain.ι ≫ X.homOfLE hle :=
      pullback.lift_snd _ _ _
    calc pullback.fst r f.domain.ι ≫ s ≫ f₁
        = (m ≫ pullback.fst p V.ι) ≫ f₁ := by rw [hmfst, Category.assoc]
      _ = (m ≫ pullback.snd p V.ι) ≫ g := by
            rw [Category.assoc, Category.assoc, hpagree']
      _ = pullback.snd r f.domain.ι ≫ X.homOfLE hle ≫ g := by
            rw [hmsnd, Category.assoc]
      _ = pullback.snd r f.domain.ι ≫ f.hom := by rw [hgf]

end Stacks.ResolutionOfSurfaces

end
