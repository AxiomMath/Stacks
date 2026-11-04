module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendFiniteEtale
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreDimensionSpecialization
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension

/-!
# Extending a cover unramified in codimension one across a regular complement

Let `X` be a locally Noetherian scheme, `U ⊆ X` a dense open and `Y → U` finite étale. If `Y`
is unramified over `X` in codimension one and the local ring `𝒪_{X, x}` is regular at every
point `x` outside `U`, then `Y` is the restriction of a finite étale cover of `X`.

## Main definitions

* `AlgebraicGeometry.PurityAtRegularLocalRings`: purity holds for every regular local ring of
  dimension at least two.
* `AlgebraicGeometry.ExtendsAcrossCodimensionOneBoundary`: a cover unramified in codimension one
  extends across the codimension-one part of the boundary.

## Main results

* `AlgebraicGeometry.exists_finiteEtale_of_isUnramifiedInCodimensionOne`: [Stacks, Tag 0H2W].
* `AlgebraicGeometry.exists_finiteEtale_of_isUnramifiedInCodimensionOne_of_isNoetherian`: the
  same conclusion for a Noetherian `X`, where the purity extension input is discharged.

## Implementation notes

"Unramified over `X` in codimension one" is not defined here: it is
`Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne`, introduced for [Stacks, Tag 0EYD] —
Lemma 58.31.1, the preceding lemma of the same section — in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullback`, line
136. It says that for every prime divisor `Z ⊆ X` whose generic point `ξ` lies outside the open
and whose local ring is a discrete valuation ring, every field factor `L_ξ` of the generic fibre
of the cover is unramified over `𝒪_{X, ξ}` in the sense of
`IsDiscreteValuationRing.IsUnramifiedWithRespectTo`, which is [Stacks, Tag 09E9].

The source argues in two stages, and the stages are carried separately here because the library
proves neither of their inputs.

* `ExtendsAcrossCodimensionOneBoundary` is the source's first stage: at a generic point `ξ` of a
  codimension-one component of `X ∖ U` the unramifiedness hypothesis makes the integral closure
  of `𝒪_{X, ξ}` in `L_ξ` finite étale, and [Stacks, Tag 0BQ5] and [Stacks, Tag 0EY3] spread the
  resulting cover of `Spec 𝒪_{X, ξ}` out over a neighbourhood. The first half of that is the
  passage from `IsUnramifiedWithRespectTo` to a finite étale integral closure, which no
  declaration of this library provides: `IsDiscreteValuationRing.IsUnramifiedWithRespectTo`, in
  `StacksFrontier.RingTheory.DiscreteValuationRing.Unramified`, is only ever consumed as a
  hypothesis. It is carried in general form, quantified over all data, rather than assumed for
  the cover at hand.
* `PurityAtRegularLocalRings` is clause (1) of [Stacks, Tag 0BMA], asserted for every regular
  local ring of dimension at least two. The library proves it in dimension exactly two —
  `Stacks.PurityDimensionTwo.hasPurity_of_ringKrullDim_eq_two` in
  `StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.PurityRegularDimensionTwo` —
  which is the base case of the source's induction on `d`; the inductive step is
  [Stacks, Tag 0BLM], available here only as
  `AlgebraicGeometry.LocalLefschetzSituation.exists_finiteEtale_extension_of_three_le_depth`,
  which takes the unrestricted [Stacks, Tag 0BLS] as a named hypothesis. So dimension `d ≥ 3` is
  out of reach and the whole of `PurityAtRegularLocalRings` is a hypothesis here.
* The extension input `hEssSurj` of the main theorem is [Stacks, Tag 0EY7] for a locally
  Noetherian base. The result `essSurj_finiteEtaleBaseChange_of_hasPurity` in
  `StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendFiniteEtale`, line
  357, proves exactly this statement under the stronger hypothesis `IsNoetherian X`, that is for
  a quasi-compact locally Noetherian `X`, which is also how the source states Lemma 58.21.6.
  Tag 0H2W asks only that `X` be locally Noetherian, so that result falls short by
  quasi-compactness alone; it is therefore a hypothesis of the main theorem and is discharged in
  `exists_finiteEtale_of_isUnramifiedInCodimensionOne_of_isNoetherian`.

What is proved here is the assembly. A point outside the enlarged open lies outside `U`, so its
local ring is regular; it is not a generic point of an irreducible component, because a dense
open of a locally Noetherian scheme contains those, so the dimension is nonzero; and it is not
of dimension one, since the enlarged open contains the codimension-one boundary. Hence purity
holds there and the purity extension applies, after which the two extension isomorphisms are
composed into a single cover of `X` restricting to the given one.

## References

* [Stacks Project, Lemma 58.31.2 (0H2W)](https://stacks.math.columbia.edu/tag/0H2W)
* [Stacks Project, Lemma 58.21.6 (0EY7)](https://stacks.math.columbia.edu/tag/0EY7)
* [Stacks Project, Lemma 58.21.3 (0BMA)](https://stacks.math.columbia.edu/tag/0BMA)
* [Stacks Project, Lemma 58.31.1 (0EYD)](https://stacks.math.columbia.edu/tag/0EYD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Purity holds for every regular local ring whose Krull dimension is at least two: every
finite étale cover of the punctured spectrum extends over the spectrum. -/
public def PurityAtRegularLocalRings : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
    (2 : WithBot ℕ∞) ≤ ringKrullDim R → HasPurity R

/-- A finite étale cover of a dense open which is unramified in codimension one over a scheme
with regular boundary local rings extends to an open containing the codimension-one boundary. -/
public def ExtendsAcrossCodimensionOneBoundary : Prop :=
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens), DenseRange U.ι.base →
    ∀ E : FiniteEtaleOver U.toScheme,
      Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne U.ι E.hom →
      (∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x)) →
      ∃ (V : X.Opens) (hUV : U ≤ V),
        (∀ x : X, x ∉ U → ringKrullDim (X.presheaf.stalk x) = 1 → x ∈ V) ∧
        ∃ F : FiniteEtaleOver V.toScheme,
          Nonempty ((finiteEtaleBaseChange (X.homOfLE hUV)).obj F ≅ E)

/-- A nonnegative element of `WithBot ℕ∞` which is neither zero nor one is at least two. -/
private lemma two_le_of_ne_zero_of_ne_one {d : WithBot ℕ∞} (hd : 0 ≤ d)
    (h0 : d ≠ 0) (h1 : d ≠ 1) : 2 ≤ d := by
  have hlt : (1 : WithBot ℕ∞) ≤ d := by
    simpa using (ENat.WithBot.add_one_le_iff (n := 0)).mpr (lt_of_le_of_ne hd (Ne.symm h0))
  rw [show (2 : WithBot ℕ∞) = 1 + 1 from rfl]
  simpa using (ENat.WithBot.add_one_le_iff (n := 1)).mpr (lt_of_le_of_ne hlt (Ne.symm h1))

/-- Outside an open containing the codimension-one boundary, a regular boundary local ring of a
scheme with dense open `U` has dimension at least two, so purity holds for it. -/
private lemma hasPurity_stalk_of_notMem
    (hPurity : PurityAtRegularLocalRings.{u}) {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U V : X.Opens} (hUV : U ≤ V) (hdense : Dense (U : Set X))
    (hreg : ∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x))
    (hcodim : ∀ x : X, x ∉ U → ringKrullDim (X.presheaf.stalk x) = 1 → x ∈ V)
    {x : X} (hx : x ∉ V) : HasPurity (X.presheaf.stalk x) := by
  have hxU : x ∉ U := fun h => hx (hUV h)
  let := hreg x hxU
  refine hPurity _ (two_le_of_ne_zero_of_ne_one ringKrullDim_nonneg_of_nontrivial
    (fun h => hxU (scheme_genericPoints_mem_dense_open X U.2 hdense
      ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints X x).mp h)))
    (fun h => hx (hcodim x hxU h)))

/-- **Stacks Project, Tag 0H2W.** Let `X` be a locally Noetherian scheme, `U ⊆ X` a dense open
and `f : Y ⟶ U` finite étale. If `Y` is unramified over `X` in codimension one and `𝒪_{X, x}` is
regular for every `x` outside `U`, then `f` is the restriction of a finite étale cover of `X`. -/
@[stacks 0H2W "extension across a regular complement, with the two inputs carried"]
public theorem exists_finiteEtale_of_isUnramifiedInCodimensionOne
    (hExtend : ExtendsAcrossCodimensionOneBoundary.{u})
    (hPurity : PurityAtRegularLocalRings.{u})
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (hdense : DenseRange U.ι.base)
    (hEssSurj : ∀ V : X.Opens, (∀ x : X, x ∉ V → HasPurity (X.presheaf.stalk x)) →
      (finiteEtaleBaseChange V.ι).EssSurj)
    {Y : Scheme.{u}} (f : Y ⟶ U) [IsFinite f] [Etale f]
    (hunr : Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne U.ι f)
    (hreg : ∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ (Y' : Scheme.{u}) (p : Y' ⟶ X), IsFinite p ∧ Etale p ∧
      ∃ e : pullback p U.ι ≅ Y, e.hom ≫ f = pullback.snd p U.ι := by
  classical
  have hdense' : Dense (U : Set X) := by rwa [DenseRange, Scheme.Opens.range_ι] at hdense
  let E : FiniteEtaleOver U.toScheme :=
    MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) f ⟨‹IsFinite f›, ‹Etale f›⟩
  obtain ⟨V, hUV, hcodim, F, ⟨iF⟩⟩ := hExtend X U hdense E hunr hreg
  obtain ⟨E', ⟨iE⟩⟩ := (hEssSurj V (fun _ hx =>
    hasPurity_stalk_of_notMem hPurity hUV hdense' hreg hcodim hx)).mem_essImage F
  let total : (finiteEtaleBaseChange U.ι).obj E' ≅ E :=
    (finiteEtaleBaseChangeComp (X.homOfLE hUV) V.ι U.ι (by simp)).app E' ≪≫
      (finiteEtaleBaseChange (X.homOfLE hUV)).mapIso iE ≪≫ iF
  exact ⟨E'.left, E'.hom, E'.prop.1, E'.prop.2,
    (Over.forget U.toScheme).mapIso
      ((MorphismProperty.Over.forget finiteEtale ⊤ U.toScheme).mapIso total),
    MorphismProperty.Over.w total.hom⟩

/-- **Stacks Project, Tag 0H2W** for a Noetherian scheme: the purity extension input is then
supplied by [Stacks, Tag 0EY7] itself. -/
public theorem exists_finiteEtale_of_isUnramifiedInCodimensionOne_of_isNoetherian
    (hExtend : ExtendsAcrossCodimensionOneBoundary.{u})
    (hPurity : PurityAtRegularLocalRings.{u})
    {X : Scheme.{u}} [IsNoetherian X] (U : X.Opens) (hdense : DenseRange U.ι.base)
    {Y : Scheme.{u}} (f : Y ⟶ U) [IsFinite f] [Etale f]
    (hunr : Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne U.ι f)
    (hreg : ∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ (Y' : Scheme.{u}) (p : Y' ⟶ X), IsFinite p ∧ Etale p ∧
      ∃ e : pullback p U.ι ≅ Y, e.hom ≫ f = pullback.snd p U.ι :=
  exists_finiteEtale_of_isUnramifiedInCodimensionOne hExtend hPurity U hdense
    (fun V h => essSurj_finiteEtaleBaseChange_of_hasPurity V.ι
      (fun x hx => h x (fun hxV => hx ⟨⟨x, hxV⟩, rfl⟩))) f hunr hreg

end AlgebraicGeometry

end
