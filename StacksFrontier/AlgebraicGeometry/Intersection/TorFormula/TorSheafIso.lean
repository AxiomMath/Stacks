module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.IntersectionProductCycle
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafSymmetry

/-!
# Isomorphic sheaves have the same `Tor` sheaves and the same alternating sum

The `Tor` sheaf `Tor_p^{𝒪_X}(ℱ, 𝒢)` is the value at `ℱ` of a composite of functors, so an
isomorphism `ℱ ≅ ℱ'` induces an isomorphism `Tor_p^{𝒪_X}(ℱ, 𝒢) ≅ Tor_p^{𝒪_X}(ℱ', 𝒢)` and hence
an equality of the alternating sums `∑ₚ (-1)ᵖ [Tor_p(ℱ, 𝒢)]_k` of Tag 0AZR.

The dévissage in the proof of Tag 0B0W needs this: its test objects are the direct images
`i_* 𝒪_Z` of the structure sheaves of integral closed subschemes, and the statement being proved
is phrased at `AlgebraicGeometry.TorFormula.structureSheafAt`, which is the direct image along
the *canonical* closed immersion of the reduced closure of a point. The two agree only up to
isomorphism.

## Main definitions

* `AlgebraicGeometry.TorFormula.torSheafMapIso` — the isomorphism of `Tor` sheaves induced by an
  isomorphism of the first argument.

## Main results

* `AlgebraicGeometry.TorFormula.intersectionProductCycle_congr_left_of_iso` — the alternating sum
  of Tag 0AZR is unchanged when the first argument is replaced by an isomorphic sheaf.

## References

* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Lemma 43.19.4 (Tag 0B0W)](https://stacks.math.columbia.edu/tag/0B0W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

variable {X : Scheme.{u}}

/-- **An isomorphism of the first argument induces an isomorphism of the `Tor` sheaves.** The
`Tor` sheaf is the value at `ℱ` of the composite of the embedding in degree zero, the derived
tensor product with `𝒢` and the `(-p)`-th homology, and a functor carries an isomorphism to an
isomorphism. -/
def torSheafMapIso {F F' : X.Modules} (e : F ≅ F') (G : X.Modules) (p : ℕ) :
    torSheaf X F G p ≅ torSheaf X F' G p :=
  (DerivedCategory.homologyFunctor X.Modules (-(p : ℤ))).mapIso
    (((derivedTensor X).mapIso
        ((DerivedCategory.singleFunctor X.Modules 0).mapIso e)).app
      ((DerivedCategory.singleFunctor X.Modules 0).obj G))

/-- **The alternating sum of Tag 0AZR is unchanged by an isomorphism of the first argument.**
Each summand is the cycle of a `Tor` sheaf, and the two `Tor` sheaves are isomorphic. -/
theorem intersectionProductCycle_congr_left_of_iso (C : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (hX : IsRegular X) {F F' : X.Modules} (e : F ≅ F') (G : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (hF' : SheafOfModules.IsCoherent F')
    (hG : SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf X F G i)).subschemeι ≫ f) ≤ WithBotTop.coe k)
    (hF'k : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F' G hF' hG i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf X F' G i)).subschemeι ≫ f) ≤ WithBotTop.coe k) :
    intersectionProductCycle C f hX F G hF hG k hFk =
      intersectionProductCycle C f hX F' G hF' hG k hF'k := by
  refine finsum_congr fun i => ?_
  have := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
  have := isCoherent_torSheaf_of_isRegular X hX F' G hF' hG i
  rw [Stacks.Chow.coherentSheafCycle_eq_of_iso C f (torSheafMapIso e G i) k (hFk i) (hF'k i)]

/-- **The delta-dimension bound transfers along an isomorphism of the first argument**, the two
families of `Tor` sheaves being isomorphic. -/
theorem torSheafDeltaDimension_le_of_iso (C : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (hX : IsRegular X) {F F' : X.Modules} (e : F ≅ F') (G : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (hF' : SheafOfModules.IsCoherent F')
    (hG : SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf X F G i)).subschemeι ≫ f) ≤ WithBotTop.coe k)
    (i : ℕ) :
    haveI := isCoherent_torSheaf_of_isRegular X hX F' G hF' hG i
    Stacks.Chow.schemeDeltaDimension C
      ((Stacks.Chow.reducedSupport (torSheaf X F' G i)).subschemeι ≫ f) ≤ WithBotTop.coe k := by
  have := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
  have := isCoherent_torSheaf_of_isRegular X hX F' G hF' hG i
  exact Stacks.Chow.schemeDeltaDimension_reducedSupport_le_of_iso C f (torSheafMapIso e G i) k
    (hFk i)

/-- The delta-dimension bound for the `Tor` sheaves of `(F, G)` gives it for those of `(G, F)`. -/
private theorem torSheafDeltaDimension_le_swap (C : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (hX : IsRegular X) (F G : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (hG : SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf X F G i)).subschemeι ≫ f) ≤ WithBotTop.coe k)
    (j : ℕ) :
    haveI := isCoherent_torSheaf_of_isRegular X hX G F hG hF j
    Stacks.Chow.schemeDeltaDimension C
      ((Stacks.Chow.reducedSupport (torSheaf X G F j)).subschemeι ≫ f) ≤ WithBotTop.coe k := by
  have := isCoherent_torSheaf_of_isRegular X hX F G hF hG j
  have := isCoherent_torSheaf_of_isRegular X hX G F hG hF j
  rw [reducedSupport_torSheaf_comm G F j]
  exact hFk j

/-- **The delta-dimension bound transfers along an isomorphism of the second argument**, by the
symmetry of the alternating sum. -/
theorem torSheafDeltaDimension_le_of_iso_right (C : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (hX : IsRegular X) (F : X.Modules) {G G' : X.Modules} (e : G ≅ G')
    (hF : SheafOfModules.IsCoherent F) (hG : SheafOfModules.IsCoherent G)
    (hG' : SheafOfModules.IsCoherent G') (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf X F G i)).subschemeι ≫ f) ≤ WithBotTop.coe k)
    (i : ℕ) :
    haveI := isCoherent_torSheaf_of_isRegular X hX F G' hF hG' i
    Stacks.Chow.schemeDeltaDimension C
      ((Stacks.Chow.reducedSupport (torSheaf X F G' i)).subschemeι ≫ f) ≤ WithBotTop.coe k := by
  have := isCoherent_torSheaf_of_isRegular X hX F G' hF hG' i
  have := isCoherent_torSheaf_of_isRegular X hX G' F hG' hF i
  rw [← reducedSupport_torSheaf_comm G' F i]
  exact torSheafDeltaDimension_le_of_iso C f hX e F hG hG' hF k
    (torSheafDeltaDimension_le_swap C f hX F G hF hG k hFk) i

/-- **The alternating sum of Tag 0AZR is unchanged by an isomorphism of the second argument**,
by the symmetry of the alternating sum. -/
theorem intersectionProductCycle_congr_right_of_iso (C : Stacks.Chow.ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X) (F : X.Modules)
    {G G' : X.Modules} (e : G ≅ G')
    (hF : SheafOfModules.IsCoherent F) (hG : SheafOfModules.IsCoherent G)
    (hG' : SheafOfModules.IsCoherent G') (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf X F G i)).subschemeι ≫ f) ≤ WithBotTop.coe k)
    (hF'k : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G' hF hG' i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf X F G' i)).subschemeι ≫ f) ≤ WithBotTop.coe k) :
    intersectionProductCycle C f hX F G hF hG k hFk =
      intersectionProductCycle C f hX F G' hF hG' k hF'k := by
  rw [intersectionProductCycle_comm C f hX F G hF hG k hFk
      (torSheafDeltaDimension_le_swap C f hX F G hF hG k hFk),
    intersectionProductCycle_comm C f hX F G' hF hG' k hF'k
      (torSheafDeltaDimension_le_swap C f hX F G' hF hG' k hF'k)]
  exact intersectionProductCycle_congr_left_of_iso C f hX e F hG hG' hF k _ _

end AlgebraicGeometry.TorFormula

end
