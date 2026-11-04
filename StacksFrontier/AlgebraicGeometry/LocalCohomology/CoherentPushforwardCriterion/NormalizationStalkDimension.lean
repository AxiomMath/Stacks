module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PushforwardStalkDepth
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.StalkDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local dimension of the normalization of a scheme in the spectrum of a residue field

Let `X` be a locally Noetherian universally catenary scheme, `p` a point of `X` and
`π : Y ⟶ X` the normalization of `X` in `Spec κ(p)`. The dimension bound

`dim 𝒪_{closure{p}, z} ≥ 2 for every z ∈ closure{p} outside an open V`

transfers to `Y`: every point `y` with `π y ∉ V` has `dim 𝒪_{Y, y} ≥ 2`. Indeed `π` factors as
`ρ : Y ⟶ closure{p}` followed by the closed immersion of the reduced point closure, and `ρ` is a
dominant finite morphism between integral schemes over a locally Noetherian universally catenary
base, so the dimension formula [Stacks, Tag 02JU] identifies `dim 𝒪_{Y, y}` with
`dim 𝒪_{closure{p}, ρ y}` — both transcendence-degree corrections vanish because `ρ` is
quasi-finite. The bound is then read off at the point `ρ y`, which lies outside `V` because
`ρ` followed by the closed immersion is `π`.

Together with Serre's criterion this is the last paragraph of the proof of [Stacks, Tag 0AWA]:
the depth hypothesis needed there for `π_*𝒪_Y` follows from the dimension bound on `Y` and
normality of `Y`.

## Main results

* `AlgebraicGeometry.isIntegral_normalization_fromSpecResidueField`: the normalization of `X` in
  `Spec κ(p)` is an integral scheme.
* `AlgebraicGeometry.two_le_ringKrullDim_stalk_normalization_fromSpecResidueField`: the
  dimension bound on the reduced closure of `{p}` outside `V`, transported to the normalization.
* `AlgebraicGeometry.hasDepthTwoOutside_pushforwardUnitModule_fromSpecResidueField`: the
  resulting depth-two hypothesis for `π_*𝒪_Y` along the complement of `V`.

## Implementation notes

Integrality of `Y` is the one input the dimension formula needs that is not already available:
`Y` is normal, hence reduced, and it is irreducible because `Spec κ(p) ⟶ Y` has trivial kernel
ideal sheaf, so its image — a single point, `Spec κ(p)` being a one-point space — is dense.

The dimension hypothesis is spelled out rather than written as
`Stacks.LocalCohomology.TwoLePointClosureDim`, which is an abbreviation living in the module
stating [Stacks, Tag 0AWA]; since that module consumes these results, importing it here would be
circular. The two spellings agree definitionally, so a `TwoLePointClosureDim V x` is accepted
directly for the hypothesis at the point `V.ι.base x`.

## References

* [Stacks Project, Tag 0AWA](https://stacks.math.columbia.edu/tag/0AWA)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
* [Stacks Project, Tag 02J9](https://stacks.math.columbia.edu/tag/02J9)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Integrality of the normalization -/

/-- The normalization of a scheme in the spectrum of a residue field is irreducible: the
canonical morphism out of `Spec κ(p)` has trivial kernel ideal sheaf, hence dense image, and
that image is a single point. -/
instance irreducibleSpace_normalization_fromSpecResidueField {X : Scheme.{u}} (p : X) :
    IrreducibleSpace (X.fromSpecResidueField p).normalization := by
  have hdom : IsDominant (X.fromSpecResidueField p).toNormalization :=
    have : IsSchemeTheoreticallyDominant (X.fromSpecResidueField p).toNormalization :=
      ⟨(X.fromSpecResidueField p).ker_toNormalization⟩
    inferInstance
  obtain ⟨z⟩ : Nonempty (Spec (X.residueField p)) := inferInstance
  have hrange : Set.range (X.fromSpecResidueField p).toNormalization.base.hom =
      {(X.fromSpecResidueField p).toNormalization.base z} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨⟨z, rfl⟩, by
      rintro - ⟨w, rfl⟩
      rw [Subsingleton.elim w z]⟩
  have hdense := (X.fromSpecResidueField p).toNormalization.denseRange
  rw [DenseRange, hrange] at hdense
  have hirr : IsIrreducible (closure
      ({(X.fromSpecResidueField p).toNormalization.base z} :
        Set (X.fromSpecResidueField p).normalization)) := isIrreducible_singleton.closure
  rw [hdense.closure_eq] at hirr
  exact (irreducibleSpace_def _).mpr (by simpa using hirr)

/-- The normalization of a scheme in the spectrum of a residue field is integral: it is
irreducible, and reduced because it is normal. -/
instance isIntegral_normalization_fromSpecResidueField {X : Scheme.{u}} (p : X) :
    IsIntegral (X.fromSpecResidueField p).normalization :=
  have : IsNormal (X.fromSpecResidueField p).normalization :=
    isNormal_normalization_fromSpecResidueField p
  isIntegral_of_irreducibleSpace_of_isReduced _

/-! ### The dimension bound -/

/-- **The dimension bound of [Stacks, Tag 0AWA] transported to the normalization.** Let `X` be
locally Noetherian and universally catenary, `V` an open subscheme and `p` a point of `X` whose
normalization in `Spec κ(p)` is finite over `X`. If every point of the reduced closure of `{p}`
outside `V` has local ring of dimension at least two, then so does every point of that
normalization lying over the complement of `V`. -/
@[ega "IV 18.9.7.6" "special case"]
theorem two_le_ringKrullDim_stalk_normalization_fromSpecResidueField {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hX : X.IsUniversallyCatenary) (V : X.Opens) (p : X)
    (hfin : IsFinite (X.fromSpecResidueField p).fromNormalization)
    (hdim : ∀ w : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({p} : Set X))).subscheme,
      (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({p} : Set X))).subschemeι.base w ∉ (V : Set X) →
        (2 : WithBot ℕ∞) ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({p} : Set X))).subscheme.presheaf.stalk w))
    (y : (X.fromSpecResidueField p).normalization)
    (hy : (X.fromSpecResidueField p).fromNormalization.base y ∉ (V : Set X)) :
    (2 : WithBot ℕ∞) ≤
      ringKrullDim ((X.fromSpecResidueField p).normalization.presheaf.stalk y) := by
  have hρfin : IsFinite (Scheme.residueFieldNormalizationToPointClosure X p) :=
    Scheme.isFinite_residueFieldNormalizationToPointClosure p hfin
  have hnoeth : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({p} : Set X))).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({p} : Set X))).subschemeι
  have hcat := Scheme.isUniversallyCatenary_of_locallyOfFiniteType
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({p} : Set X))).subschemeι hX
  rw [ringKrullDim_stalk_eq_of_locallyQuasiFinite
    (Scheme.residueFieldNormalizationToPointClosure X p) hcat y]
  refine hdim _ ?_
  have hpt : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({p} : Set X))).subschemeι.base
        ((Scheme.residueFieldNormalizationToPointClosure X p).base y) =
      (X.fromSpecResidueField p).fromNormalization.base y :=
    congrArg (fun g : (X.fromSpecResidueField p).normalization ⟶ X => g.base y)
      (Scheme.residueFieldNormalizationToPointClosure_subschemeι X p)
  rw [hpt]
  exact hy

/-- **The last paragraph of the proof of [Stacks, Tag 0AWA].** Over a locally Noetherian
universally catenary scheme, the dimension bound on the reduced closure of `{p}` outside `V`
gives depth at least two for the stalks of `π_*𝒪_Y` along the complement of `V`, where
`π : Y ⟶ X` is the normalization of `X` in `Spec κ(p)`, assumed finite. -/
theorem hasDepthTwoOutside_pushforwardUnitModule_fromSpecResidueField {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hX : X.IsUniversallyCatenary) (V : X.Opens) (p : X)
    (hfin : IsFinite (X.fromSpecResidueField p).fromNormalization)
    (hdim : ∀ w : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({p} : Set X))).subscheme,
      (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({p} : Set X))).subschemeι.base w ∉ (V : Set X) →
        (2 : WithBot ℕ∞) ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({p} : Set X))).subscheme.presheaf.stalk w)) :
    HasDepthTwoOutside X
      (X.fromSpecResidueField p).fromNormalization.pushforwardUnitModule V :=
  have := hfin
  (X.fromSpecResidueField p).fromNormalization.hasDepthTwoOutside_pushforwardUnitModule_of_isNormal
    (isNormal_normalization_fromSpecResidueField p) V
    (two_le_ringKrullDim_stalk_normalization_fromSpecResidueField hX V p hfin hdim)

end AlgebraicGeometry

end
