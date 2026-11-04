module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackRelative

/-!
# Decompositions of open substacks of curves into open and closed substacks

Several lemmas of the chapter on moduli of curves decompose an open substack `Curves^P` of the
stack of curves into open and closed substacks indexed by an invariant, typically the genus:
`Curves^{grc, 1} = ∐_g Curves^{grc, 1}_g` (Stacks 0E1K), `Curves^{prestable} = ∐_g
Curves^{prestable}_g` (Stacks 0E6V), `𝓜̄ = ∐_{g ≥ 2} 𝓜̄_g` (Stacks 0E78) and `𝓜 = ∐_g 𝓜_g`
(Stacks 0E83). In each case the source argues in the same way, through the discussion of Section
0E0E: over the base `S` of a family with `P` the invariant cuts out loci of points of `S` which
are open, pairwise disjoint, cover `S`, and whose formation commutes with base change; and the
pieces `Curves^{P, Q_i}` are cut out by asking the base to lie in one locus.

This module proves that step once, in the form of condition (o) of Stacks 0E0E.

## Main results

* `AlgebraicGeometry.IsOpenCurvesLocus.and_of_baseLocus_of_imp`: condition (o) for `P ∧ Q` when
  `Q` is read off a locus of points of the base only among the families with `P`.
* `AlgebraicGeometry.IsOpenCurvesLocus.openClosedDecomposition_of_baseLoci`: the decomposition
  of `Curves^P` into the open and closed substacks `Curves^{P, Q_i}`.

## Implementation notes

The decomposition is stated through condition (o), which by Stacks 0E0E
(`AlgebraicGeometry.isOpenImmersion_curvesSubstackInclusion_and_factors_iff`) makes every
`Curves^{P, Q_i}` an open substack of `Curves` with the universal property (1) of the source.
That the pieces are open *and closed* substacks of `Curves^P`, pairwise disjoint and covering it,
is read on the scheme-valued points of `Curves^P`: over the base of every family with `P` the loci
are clopen, pairwise disjoint and cover, and a family mapping to it lies in `Curves^{P, Q_i}`
exactly when its base lands in the `i`-th locus.

The loci are sets of points (Stacks 03BU) of the base, with the topology of
`AlgebraicGeometry.Space.pointTopology`; on the base scheme of a family of curves this is the
Zariski topology of that scheme.

## References

* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E1K](https://stacks.math.columbia.edu/tag/0E1K)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Condition (o) for a locus read off the base among the families with `P`.** Let `P` satisfy
condition (o) of Stacks 0E0E, and let `L` be a locus of points of the base of every family of
curves which commutes with base change along morphisms of families. If `L(G)` is open whenever `G`
has `P`, and among the families with `P` the property `Q` says that `L` is everything, then
`P ∧ Q` satisfies condition (o). -/
theorem IsOpenCurvesLocus.and_of_baseLocus_of_imp {P Q : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P)
    (L : ∀ G : CurveFamily B hZ, Set (Space.points B integerBase hZ (schemeSpace G.base).obj))
    (hL : ∀ {F G : CurveFamily B hZ} (a : F ⟶ G),
      Space.pointsMap B integerBase hZ (schemeSpace F.base).obj (schemeSpaceMap a.baseMap).hom ⁻¹'
        L G = L F)
    (hQ : ∀ F : CurveFamily B hZ, P F → (Q F ↔ L F = Set.univ))
    (hopen : ∀ G : CurveFamily B hZ, P G → IsOpen (L G)) :
    IsOpenCurvesLocus B hZ (fun F => P F ∧ Q F) := by
  intro G
  obtain ⟨W, hW, hchar⟩ :=
    hP.and_of_baseLocus L hL (Q := fun F => L F = Set.univ) (fun _ => Iff.rfl) hopen G
  exact ⟨W, hW, fun F a => (and_congr_right (hQ F)).trans (hchar F a)⟩

/-- **A decomposition of `Curves^P` into open and closed substacks.** Let `P` satisfy condition (o)
of Stacks 0E0E and let `L i`, `i : ι`, be loci of points of the base of every family of curves,
commuting with base change along morphisms of families, which over the base of every family with
`P` are open, pairwise disjoint and cover the base. Let `Q i` be properties which, among the
families with `P`, say that the base is the locus `L i`. Then

* every `P ∧ Q i` satisfies condition (o), so `Curves^{P, Q_i}` is an open substack of `Curves`;
* over the base of every family `G` with `P` the loci `L i G` are open and closed, pairwise
  disjoint, and cover the base;
* a family `F` mapping to such a `G` lies in `Curves^{P, Q_i}` exactly when its base lands in
  `L i G`.

That is, `Curves^P = ∐_i Curves^{P, Q_i}` as a decomposition into open and closed substacks. -/
theorem IsOpenCurvesLocus.openClosedDecomposition_of_baseLoci {ι : Type*}
    {P : ObjectProperty (CurveFamily B hZ)} (hP : IsOpenCurvesLocus B hZ P)
    (L : ι → ∀ G : CurveFamily B hZ,
      Set (Space.points B integerBase hZ (schemeSpace G.base).obj))
    (hL : ∀ (i : ι) {F G : CurveFamily B hZ} (a : F ⟶ G),
      Space.pointsMap B integerBase hZ (schemeSpace F.base).obj (schemeSpaceMap a.baseMap).hom ⁻¹'
        L i G = L i F)
    (hopen : ∀ (i : ι) (G : CurveFamily B hZ), P G → IsOpen (L i G))
    (hdisj : ∀ G : CurveFamily B hZ, P G → Pairwise (Function.onFun Disjoint fun i => L i G))
    (hcover : ∀ G : CurveFamily B hZ, P G → ⋃ i, L i G = Set.univ)
    (Q : ι → ObjectProperty (CurveFamily B hZ))
    (hQ : ∀ (i : ι) (F : CurveFamily B hZ), P F → (Q i F ↔ L i F = Set.univ)) :
    (∀ i : ι, IsOpenCurvesLocus B hZ (fun F => P F ∧ Q i F)) ∧
      ∀ G : CurveFamily B hZ, P G →
        (∀ i : ι, IsClopen (L i G)) ∧ Pairwise (Function.onFun Disjoint fun i => L i G) ∧
          ⋃ i, L i G = Set.univ ∧
          ∀ (i : ι) (F : CurveFamily B hZ) (a : F ⟶ G),
            (P F ∧ Q i F ↔ Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
              (schemeSpaceMap a.baseMap).hom) ⊆ L i G) := by
  refine ⟨fun i => hP.and_of_baseLocus_of_imp (L i) (hL i) (hQ i) (hopen i), fun G hG => ?_⟩
  refine ⟨fun i => ⟨?_, hopen i G hG⟩, hdisj G hG, hcover G hG, fun i F a => ?_⟩
  · have hcompl : (L i G)ᶜ = ⋃ (j : ι) (_ : j ≠ i), L j G := by
      ext s
      simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
      constructor
      · intro hs
        obtain ⟨j, hj⟩ := Set.iUnion_eq_univ_iff.mp (hcover G hG) s
        exact ⟨j, fun hji => hs (hji ▸ hj), hj⟩
      · rintro ⟨j, hji, hj⟩ hs
        exact Set.disjoint_left.mp (hdisj G hG hji) hj hs
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j G hG
  · have hF : P F := hP.prop_of_hom a hG
    rw [and_iff_right hF, hQ i F hF, ← hL i a, Set.preimage_eq_univ_iff]

end AlgebraicGeometry

end
