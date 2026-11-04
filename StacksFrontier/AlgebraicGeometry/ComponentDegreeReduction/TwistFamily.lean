module

public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.SupportBounds
public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessCoproduct.Basic

/-!
# [Stacks, Tag 0AYW], paragraph 1 with [Stacks, Tag 02O6] replaced by a family of twists

`StacksFrontier/AlgebraicGeometry/ComponentDegreeReduction/SupportBounds.lean` proves paragraph 1
of [Stacks, Tag 0AYW] for a finite family of closed subschemes from two hypotheses: a geometric
one about the comparison map `𝒪_X ⟶ g_*𝒪_{X'}`, and finite dimensionality of the cohomology of
*every* coherent module on `X`, which is [Stacks, Tag 02O6] over a field. The second hypothesis is
not geometry of paragraph 1 at all; it is the input every Euler characteristic in the chain needs
in order to be a finite sum.

This file removes it, in favour of the hypotheses the source's own route to [Stacks, Tag 02O6]
supplies: a family `𝒯` of coherent modules whose cohomology is finite-dimensional in every degree,
such that every coherent module is a quotient of a finite coproduct of members of `𝒯`. On
projective space those are the Čech computation of [Stacks, Tag 01XT] and clause (1) of
[Stacks, Tag 01YS] — at the *heterogeneous* shape, with the degrees of the summands allowed to
vary, which is what clause (1) says; the single-degree form is the stronger [Stacks, Tag 01QB].

The replacement needs no bridging lemma and no respelling:
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_coproduct` concludes
exactly the proposition that stands in the `h02O6` binder of
`AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective`, so each
theorem below is that theorem applied to that one.

## Main results

* `AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective_of_coproduct`:
  paragraph 1's degree formula with the family of twists on `X` itself.
* `AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective_of_embedding`:
  the same with the family on an **ambient** proper scheme into which `X` is closed-immersed. This
  is the shape the source's route delivers, because a proper scheme of dimension at most one need
  not carry a family of twists itself — it is embedded in projective space and the family lives
  there.
* `AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_id_of_coproduct`: the geometric
  hypothesis discharged at the one-member family `fun _ => 𝟙 X`, so that the statements above are
  not statements about an empty family of inputs.

## Implementation notes

**No tag attribute is attached to anything here, and this file proves no tag.** Each statement
still carries the geometric hypothesis of paragraph 1 — that the comparison map attached to the
family is bijective on stalks outside a finite set of closed points — as an explicit hypothesis,
and still sums over `Finset.range N` with the components presented as a function `ℕ → Scheme`
rather than over the generic points of the reduced one-dimensional components weighted by their
multiplicities. Nothing here says anything about paragraph 2. The attributes for
[Stacks, Tag 01XT] and for clause (1) of [Stacks, Tag 01YS] belong on the statements that prove
them on projective space, namely `Stacks.ProjectiveSpace.Cohomology.twistCohomologyMonomial` and
`Stacks.ProjectiveSpace.exists_epi_biproduct_tensorPowModule`, and they are carried there.

**What is and is not shown satisfiable.** The geometric hypothesis is discharged outright at the
one-member family `fun _ => 𝟙 X`, for every proper `X` of dimension at most one, by
`AlgebraicGeometry.bijective_stalk_pushforwardUnitSeriesMap_id`. The family hypotheses are
satisfiable by `AlgebraicGeometry.exists_coproduct_family_of_forall_finiteDimensional` on every
`X` whose coherent cohomology is *already* known to be finite-dimensional — which is conditional,
and in particular does **not** exhibit an unconditional inhabitant. On projective space the
witnessing family is the twists, whose cohomology is computed by [Stacks, Tag 01XT]
(`Stacks.ProjectiveSpace.Cohomology.twistCohomologyMonomial`, with the finiteness
`Stacks.ProjectiveSpace.Cohomology.moduleFinite_twistCohomology`); assembling those into the
coproduct hypothesis below is not done here. So the hypothesis set is consistent and holds
wherever the conclusion of [Stacks, Tag 02O6] does, and no unconditional witness for the family
is exhibited here.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-- **Paragraph 1 of [Stacks, Tag 0AYW] for a finite family, with [Stacks, Tag 02O6] replaced by a
family of twists on `X`**: `deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`.

This is `AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective` with
its `h02O6` hypothesis — finite dimensionality of the cohomology of every coherent module on `X` —
replaced by the three hypotheses of
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_coproduct`, which imply it.
The geometric hypothesis of paragraph 1 is untouched and is still a hypothesis: a finite set `Z`
of closed points of `X` off which the comparison map `𝒪_X ⟶ g_*𝒪_{X'}` is bijective on stalks. -/
theorem curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective_of_coproduct
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] {ι : Type v} (T : ι → X.Modules) {Zs : ℕ → Scheme.{u}}
    (i : ∀ j, Zs j ⟶ X) [∀ j, IsClosedImmersion (i j)]
    (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] (N : ℕ)
    (Z : Set X) (hZfin : Z.Finite) (hZcl : ∀ x ∈ Z, IsClosed ({x} : Set X))
    (hbij : ∀ x ∉ Z, Function.Bijective (ConcreteCategory.hom
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map
        (Scheme.Modules.pushforwardUnitSeriesMap i N))))
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (m : ℕ), FiniteDimensional k (cohomologyOverField k f (T a) m))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    curveDegree k f hX E n =
      ∑ j ∈ Finset.range N, @curveDegree k _ (Zs j) (i j ≫ f) _
        (le_trans (IsClosedImmersion.isClosedEmbedding
          (i j)).isInducing.topologicalKrullDim_le hX)
        ((Scheme.Modules.pullback (i j)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback (i j) E n) :=
  curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective k f i hX E n N Z hZfin hZcl hbij
    (forall_finiteDimensional_cohomologyOverField_of_epi_coproduct k f T hTcoh hTfin hgen)

/-- **Paragraph 1 of [Stacks, Tag 0AYW] for a finite family, with [Stacks, Tag 02O6] replaced by a
family of twists on an ambient proper scheme.** A proper scheme of dimension at most one need not
carry a family of twists itself; what the source does is embed it. If `j : X ⟶ Y` is a closed
immersion into a locally Noetherian `Y` proper over `k`, over `Spec k`, and `Y` carries a family
`𝒯` of coherent modules with finite-dimensional cohomology such that every coherent module on `Y`
is a quotient of a finite coproduct of members of `𝒯`, then paragraph 1's degree formula holds on
`X`.

`Spec k` is not terminal in the category of schemes, so the factorisation `j ≫ fY = f` is a
hypothesis and not automatic; it is what
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_coproduct`
transports the finiteness along. `[IsProper f]` is a separate binder and is load-bearing:
`curveDegree k f` needs it to elaborate at all, and instance search does not produce it from
`[IsProper fY]`, `[IsClosedImmersion j]` and the equation `hj`: without the binder there are
three `failed to synthesize instance IsProper f` errors. -/
theorem curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective_of_embedding
    (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [IsProper f] [IsLocallyNoetherian Y] [IsProper fY] {ι : Type v} (T : ι → Y.Modules)
    (j : X ⟶ Y) [IsClosedImmersion j] (hj : j ≫ fY = f) {Zs : ℕ → Scheme.{u}}
    (i : ∀ l, Zs l ⟶ X) [∀ l, IsClosedImmersion (i l)]
    (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] (N : ℕ)
    (Z : Set X) (hZfin : Z.Finite) (hZcl : ∀ x ∈ Z, IsClosed ({x} : Set X))
    (hbij : ∀ x ∉ Z, Function.Bijective (ConcreteCategory.hom
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map
        (Scheme.Modules.pushforwardUnitSeriesMap i N))))
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (m : ℕ), FiniteDimensional k (cohomologyOverField k fY (T a) m))
    (hgen : ∀ G : Y.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun l => T (d l)) ⟶ G, Epi φ) :
    curveDegree k f hX E n =
      ∑ l ∈ Finset.range N, @curveDegree k _ (Zs l) (i l ≫ f) _
        (le_trans (IsClosedImmersion.isClosedEmbedding
          (i l)).isInducing.topologicalKrullDim_le hX)
        ((Scheme.Modules.pullback (i l)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback (i l) E n) :=
  curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective k f i hX E n N Z hZfin hZcl hbij
    (forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_coproduct k fY T j f hj
      hTcoh hTfin hgen)

/-- **The geometric hypothesis of
`AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective_of_coproduct` is
satisfiable with `Z = ∅`**, at the one-member family `fun _ => 𝟙 X`, for every proper `X` of
dimension at most one.

This is the inhabitant of that theorem's geometric hypothesis, so that the theorem is not a
statement about an empty family of inputs. It is not a step of paragraph 1, whose families are the
closures of the complements of the other components. The family hypotheses are *not* discharged
here and no unconditional witness for them exists in either tree; see the module documentation. -/
theorem curveDegree_eq_sum_pushforwardUnitSeriesMap_id_of_coproduct
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    {ι : Type v} (T : ι → X.Modules)
    (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (m : ℕ), FiniteDimensional k (cohomologyOverField k f (T a) m))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    curveDegree k f hX E n =
      ∑ j ∈ Finset.range 1, @curveDegree k _ ((fun _ : ℕ => X) j)
        ((fun _ : ℕ => 𝟙 X) j ≫ f) _
        (le_trans (IsClosedImmersion.isClosedEmbedding
          ((fun _ : ℕ => 𝟙 X) j)).isInducing.topologicalKrullDim_le hX)
        ((Scheme.Modules.pullback ((fun _ : ℕ => 𝟙 X) j)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback ((fun _ : ℕ => 𝟙 X) j) E n) :=
  curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective_of_coproduct k f T
    (fun _ : ℕ => 𝟙 X) hX E n 1 ∅ Set.finite_empty (by simp)
    (fun x _ => bijective_stalk_pushforwardUnitSeriesMap_id X x) hTcoh hTfin hgen

/-- **The whole hypothesis set of
`AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective_of_coproduct` is
jointly satisfiable**, on every proper `X` whose coherent cohomology over `k` is already
finite-dimensional in every degree: the family of all coherent modules satisfies the three family
hypotheses by `AlgebraicGeometry.exists_coproduct_family_of_forall_finiteDimensional`, and the
one-member family `fun _ => 𝟙 X` satisfies the geometric one with `Z = ∅`.

This is a consistency check on the hypotheses: a hypothesis set can be sorry-free and still be
satisfied by nothing at all. What it does **not** do is exhibit an unconditional inhabitant — the
finiteness `h` is a hypothesis here, and on projective space the witnessing family is the twists
and the finiteness of their cohomology is exactly the absent [Stacks, Tag 01XT]. So the set is
consistent and holds wherever the conclusion of [Stacks, Tag 02O6] does, and no more than that is
claimed. -/
theorem exists_coproduct_family_and_stalk_bijective_of_forall_finiteDimensional
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (h : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m)) :
    ∃ (J : Type (u + 1)) (S : J → X.Modules) (Z : Set X),
      Z.Finite ∧ (∀ x ∈ Z, IsClosed ({x} : Set X)) ∧
      (∀ x ∉ Z, Function.Bijective (ConcreteCategory.hom
        ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map
          (Scheme.Modules.pushforwardUnitSeriesMap (fun _ : ℕ => 𝟙 X) 1)))) ∧
      (∀ a : J, SheafOfModules.IsCoherent (S a)) ∧
      (∀ (a : J) (m : ℕ), FiniteDimensional k (cohomologyOverField k f (S a) m)) ∧
      ∀ G : X.Modules, SheafOfModules.IsCoherent G →
        ∃ (r : ℕ) (d : Fin r → J), ∃ φ : (∐ fun j => S (d j)) ⟶ G, Epi φ := by
  obtain ⟨J, S, hScoh, hSfin, hSgen⟩ := exists_coproduct_family_of_forall_finiteDimensional k f h
  exact ⟨J, S, ∅, Set.finite_empty, by simp,
    fun x _ => bijective_stalk_pushforwardUnitSeriesMap_id X x, hScoh, hSfin, hSgen⟩

/-- **The spectrum of a field has dimension at most one**, so it is a legitimate base for
`AlgebraicGeometry.curveDegree`. The topological Krull dimension of a prime spectrum is the ring's
Krull dimension, which for a field is zero. -/
theorem topologicalKrullDim_specBase_le_one (k : Type u) [Field k] :
    topologicalKrullDim (Spec (CommRingCat.of k)) ≤ 1 := by
  show topologicalKrullDim (PrimeSpectrum k) ≤ 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  decide

/-- **Every instance binder of
`AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective_of_coproduct` is
inhabited simultaneously on a concrete scheme**, and after that the family triple is the only
hypothesis left: `Spec k` is proper over `k` by the identity, has dimension zero, its structure
sheaf is finite locally free of rank one, the identity is a closed immersion, and the geometric
hypothesis holds with `Z = ∅`.

**What this does not show, stated because it matters.** `Spec k` is irreducible and
zero-dimensional, so it exercises **none** of paragraph 1's multi-component content — the whole
point of the theorem is a family of components, and here the family has one member which is the
whole scheme. It is a check that the binder classes are jointly inhabited, not a check that the
geometry is non-degenerate — and a one-component scheme cannot exercise content about several
components. The non-degenerate witness would be a proper scheme of dimension *exactly* one, and
until today the library had none: the only unconditional inhabitants of
`AlgebraicGeometry.IsCurve` were `AlgebraicGeometry.isCurve_specPolynomial` and
`AlgebraicGeometry.isCurve_affineSpace`, both the affine line, which
`AlgebraicGeometry.not_isProper_affineSpace` proves is not proper. `ℙ¹_k` closes that gap and is
still irreducible, so it would not exercise the component content either. -/
theorem curveDegree_eq_sum_pushforwardUnitSeriesMap_specBase_of_coproduct
    (k : Type u) [Field k] {ι : Type v} (T : ι → (Spec (CommRingCat.of k)).Modules)
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (m : ℕ), FiniteDimensional k
      (cohomologyOverField k (𝟙 (Spec (CommRingCat.of k))) (T a) m))
    (hgen : ∀ G : (Spec (CommRingCat.of k)).Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    curveDegree k (𝟙 (Spec (CommRingCat.of k))) (topologicalKrullDim_specBase_le_one k)
        (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf) 1 =
      ∑ j ∈ Finset.range 1,
        @curveDegree k _ ((fun _ : ℕ => Spec (CommRingCat.of k)) j)
          ((fun _ : ℕ => 𝟙 (Spec (CommRingCat.of k))) j ≫ 𝟙 (Spec (CommRingCat.of k))) _
          (le_trans (IsClosedImmersion.isClosedEmbedding
            ((fun _ : ℕ => 𝟙 (Spec (CommRingCat.of k))) j)).isInducing.topologicalKrullDim_le
            (topologicalKrullDim_specBase_le_one k))
          ((Scheme.Modules.pullback ((fun _ : ℕ => 𝟙 (Spec (CommRingCat.of k))) j)).obj
            (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf)) 1
          (isFiniteLocallyFreeOfRank_pullback
            ((fun _ : ℕ => 𝟙 (Spec (CommRingCat.of k))) j)
            (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf) 1) :=
  curveDegree_eq_sum_pushforwardUnitSeriesMap_id_of_coproduct k (𝟙 (Spec (CommRingCat.of k))) T
    (topologicalKrullDim_specBase_le_one k)
    (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf) 1 hTcoh hTfin hgen

end AlgebraicGeometry

end
