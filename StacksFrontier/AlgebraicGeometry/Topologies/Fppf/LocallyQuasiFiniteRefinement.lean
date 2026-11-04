module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.QuasiFiniteSlice
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.QuasiFiniteSlices
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.EtaleFiniteFreeDomination

/-!
# Locally quasi-finite refinements of fppf coverings

[Stacks, Tag 0572] says that every fppf covering `{S_i → S}` is refined by an fppf covering
`{T_j → S}` whose members are locally quasi-finite over `S`.

The proof applies [Stacks, Tag 0571] at every point of `S`. The slicing lemma
[Stacks, Tag 0570] enters as the hypothesis `AlgebraicGeometry.HasQuasiFiniteSlices` of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.QuasiFiniteSlice`, which is
`AlgebraicGeometry.hasQuasiFiniteSlices` of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.QuasiFiniteSlices`.

An fppf covering of `S` is an `S.Cover Scheme.fppfPrecoverage`, that is a jointly surjective
family of flat morphisms locally of finite presentation; refinement is a
`CategoryTheory.PreZeroHypercover.Hom` between the underlying families over `S`, the notion
recorded in `StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver`.

From Tag 0572 follow [Stacks, Tag 0DET], through the reduction of
`StacksFrontier.AlgebraicGeometry.Topologies.Fppf.EtaleFiniteFreeDomination`, and
[Stacks, Tag 05WN]. Each of the three results is stated both with
`AlgebraicGeometry.HasQuasiFiniteSlices` as an explicit hypothesis and without it.

## Main results

* `AlgebraicGeometry.hasLocallyQuasiFiniteRefinement` is [Stacks, Tag 0572]: every fppf
  covering of a scheme is refined by an fppf covering whose members are locally quasi-finite.
* `AlgebraicGeometry.hasLocallyQuasiFiniteRefinement_of_hasQuasiFiniteSlices` is the same
  statement with `AlgebraicGeometry.HasQuasiFiniteSlices` as an explicit hypothesis.
* `Stacks.Topologies.Fppf.etaleFiniteLocallyFreeDominates` is [Stacks, Tag 0DET]: every fppf
  covering is refined by composites of an étale covering with surjective finite locally free
  morphisms.
* `Stacks.Topologies.Fppf.etaleFiniteLocallyFreeDominates_of_hasQuasiFiniteSlices` is the same
  statement with `AlgebraicGeometry.HasQuasiFiniteSlices` as an explicit hypothesis.
* `Stacks.Topologies.Fppf.exists_openCover_finiteLocallyFree_refinement` is [Stacks, Tag 05WN]:
  an fppf covering is refined by a family obtained by successively taking a Zariski open cover,
  a surjective finite locally free morphism, another Zariski open cover, and another surjective
  finite locally free morphism.
* `Stacks.Topologies.Fppf.exists_openCover_finiteLocallyFree_refinement_of_hasQuasiFiniteSlices`
  is the same statement with `AlgebraicGeometry.HasQuasiFiniteSlices` as an explicit
  hypothesis.

## Implementation notes

The refining family is indexed by the points of the base scheme, so it is an
`S.Cover.{u} Scheme.fppfPrecoverage` independently of the indexing universe `v` of the given
family. The choice of a factorization at each point is made with `Classical.choice` through an
auxiliary structure, so that the data and its properties are carried together.

## References

* [Stacks Project, Tag 0572](https://stacks.math.columbia.edu/tag/0572)
* [Stacks Project, Tag 0571](https://stacks.math.columbia.edu/tag/0571)
* [Stacks Project, Tag 0DET](https://stacks.math.columbia.edu/tag/0DET)
* [Stacks Project, Tag 05WN](https://stacks.math.columbia.edu/tag/05WN)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- The data chosen at a point `s` of the base: an index `i` of the given family, a scheme `T`
over `S` which is fppf and locally quasi-finite over `S`, a factorization of `T ⟶ S` through
the `i`-th member, and a point of `T` above `s`. -/
private structure FppfRefinementData {S : Scheme.{u}}
    (𝒰 : S.Cover.{v} Scheme.fppfPrecoverage) (s : S) where
  /-- The index of the member of `𝒰` that the chosen morphism factors through. -/
  i : 𝒰.I₀
  /-- The source of the chosen morphism. -/
  T : Scheme.{u}
  /-- The chosen morphism to the base. -/
  g : T ⟶ S
  /-- The chosen factorization through the `i`-th member of `𝒰`. -/
  h : T ⟶ 𝒰.X i
  /-- The factorization commutes. -/
  fac : h ≫ 𝒰.f i = g
  /-- The chosen morphism is fppf. -/
  fppf : Flat g ∧ LocallyOfFinitePresentation g
  /-- The chosen morphism is locally quasi-finite. -/
  quasiFinite : LocallyOfFiniteType g ∧ LocallyQuasiFinite g
  /-- The point `s` is in the image of the chosen morphism. -/
  covers : s ∈ Set.range g

/-- **Stacks Project, Tag 0572**, granted [Stacks, Tag 0570] in the form
`AlgebraicGeometry.HasQuasiFiniteSlices`. Every fppf covering of a scheme has an fppf
refinement whose members are locally quasi-finite over the scheme.

The form without the hypothesis is `AlgebraicGeometry.hasLocallyQuasiFiniteRefinement`. -/
theorem hasLocallyQuasiFiniteRefinement_of_hasQuasiFiniteSlices
    (h0570 : HasQuasiFiniteSlices.{u}) {S : Scheme.{u}}
    (𝒰 : S.Cover.{v} Scheme.fppfPrecoverage) :
    HasLocallyQuasiFiniteRefinement 𝒰 := by
  classical
  have hmap (i : 𝒰.I₀) : Flat (𝒰.f i) ∧ LocallyOfFinitePresentation (𝒰.f i) := 𝒰.map_prop i
  have : Scheme.JointlySurjective Scheme.fppfPrecoverage := by
    show Scheme.JointlySurjective (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
    infer_instance
  have hd (s : S) : Nonempty (FppfRefinementData 𝒰 s) := by
    obtain ⟨i, hi⟩ := 𝒰.exists_eq s
    have := (hmap i).1
    have := (hmap i).2
    obtain ⟨T, g, h, hfac, hflat, hlfp, hlft, hlqf, hrange⟩ :=
      exists_flat_locallyQuasiFinite_factorization_through_of_hasQuasiFiniteSlices
        h0570 (𝒰.f i) s hi
    exact ⟨⟨i, T, g, h, hfac, ⟨hflat, hlfp⟩, ⟨hlft, hlqf⟩, hrange⟩⟩
  let d (s : S) : FppfRefinementData 𝒰 s := Classical.choice (hd s)
  let 𝒱 : S.Cover.{u} Scheme.fppfPrecoverage :=
    Scheme.Cover.mkOfCovers S (fun s => (d s).T) (fun s => (d s).g)
      (fun s => ⟨s, (d s).covers⟩) (fun s => (d s).fppf)
  exact ⟨𝒱, ⟨⟨fun s => (d s).i, fun s => (d s).h, fun s => (d s).fac⟩⟩,
    fun j => (d j).quasiFinite⟩

/-- **Stacks Project, Tag 0572.** An fppf covering `𝒰` of a scheme `S` is refined by an fppf
covering `{T_j ⟶ S}`, indexed by the points of `S`, each member of which is locally
quasi-finite over `S`. -/
@[stacks 0572]
theorem hasLocallyQuasiFiniteRefinement {S : Scheme.{u}}
    (𝒰 : S.Cover.{v} Scheme.fppfPrecoverage) :
    HasLocallyQuasiFiniteRefinement 𝒰 :=
  hasLocallyQuasiFiniteRefinement_of_hasQuasiFiniteSlices hasQuasiFiniteSlices 𝒰

end AlgebraicGeometry

namespace Stacks.Topologies.Fppf

/-- **Stacks Project, Tag 0DET**, granted [Stacks, Tag 0570] in the form
`AlgebraicGeometry.HasQuasiFiniteSlices`. An fppf covering is refined by composites of an
étale covering with surjective finite locally free morphisms.

The form without the hypothesis is `Stacks.Topologies.Fppf.etaleFiniteLocallyFreeDominates`. -/
theorem etaleFiniteLocallyFreeDominates_of_hasQuasiFiniteSlices
    (h0570 : HasQuasiFiniteSlices.{u}) {S : Scheme.{u}}
    (𝒰 : S.Cover.{v} Scheme.fppfPrecoverage) :
    EtaleFiniteLocallyFreeDominates 𝒰 :=
  etaleFiniteLocallyFreeDominates_of_hasLocallyQuasiFiniteRefinement 𝒰
    (hasLocallyQuasiFiniteRefinement_of_hasQuasiFiniteSlices h0570 𝒰)

/-- **Stacks Project, Tag 0DET.** An fppf covering `{S_i ⟶ S}` is refined by an fppf covering
`{V_a ⟶ S}` whose members factor as `V_a ⟶ S'_a ⟶ S` with `{S'_a ⟶ S}` an étale covering and
`V_a ⟶ S'_a` surjective finite locally free. -/
@[stacks 0DET]
theorem etaleFiniteLocallyFreeDominates {S : Scheme.{u}}
    (𝒰 : S.Cover.{v} Scheme.fppfPrecoverage) :
    EtaleFiniteLocallyFreeDominates 𝒰 :=
  etaleFiniteLocallyFreeDominates_of_hasLocallyQuasiFiniteRefinement 𝒰
    (hasLocallyQuasiFiniteRefinement 𝒰)

/-- **Stacks Project, Tag 05WN**, granted [Stacks, Tag 0570] in the form
`AlgebraicGeometry.HasQuasiFiniteSlices`: an fppf covering is refined by a family obtained by
successively taking a Zariski open cover, a surjective finite locally free morphism, another
Zariski open cover, and another surjective finite locally free morphism.

The form without the hypothesis is
`Stacks.Topologies.Fppf.exists_openCover_finiteLocallyFree_refinement`. -/
theorem exists_openCover_finiteLocallyFree_refinement_of_hasQuasiFiniteSlices
    (h0570 : HasQuasiFiniteSlices.{u}) (S : Scheme.{u})
    (𝒮 : S.Cover.{v} Scheme.fppfPrecoverage) :
    ∃ (𝒰 : S.OpenCover.{max u v})
      (W : 𝒰.I₀ → Scheme.{u})
      (g : ∀ j, W j ⟶ 𝒰.X j)
      (𝒲 : ∀ j, (W j).OpenCover.{max u v})
      (T : ∀ j, (𝒲 j).I₀ → Scheme.{u})
      (h : ∀ j k, T j k ⟶ (𝒲 j).X k),
      (∀ j, Surjective (g j) ∧ Stacks.Morphisms.IsFiniteLocallyFree (g j)) ∧
      (∀ j k, Surjective (h j k) ∧ Stacks.Morphisms.IsFiniteLocallyFree (h j k)) ∧
      Presieve.ofArrows
          (fun jk : Σ j, (𝒲 j).I₀ ↦ T jk.1 jk.2)
          (fun jk ↦ h jk.1 jk.2 ≫ (𝒲 jk.1).f jk.2 ≫ g jk.1 ≫ 𝒰.f jk.1) ∈
        Scheme.fppfPrecoverage S ∧
      ∀ j k, ∃ i, ∃ l : T j k ⟶ 𝒮.X i,
        l ≫ 𝒮.f i = h j k ≫ (𝒲 j).f k ≫ g j ≫ 𝒰.f j :=
  exists_openCover_finiteLocallyFree_refinement_of_locallyQuasiFinite S 𝒮
    (hasLocallyQuasiFiniteRefinement_of_hasQuasiFiniteSlices h0570 𝒮)

/-- **Stacks Project, Tag 05WN.** Let `𝒮 = {S_i ⟶ S}` be an fppf covering of a scheme. Then
there are a Zariski open covering `S = ⋃ U_j`, surjective finite locally free morphisms
`W_j ⟶ U_j`, Zariski open coverings `W_j = ⋃_k W_{j,k}`, and surjective finite locally free
morphisms `T_{j,k} ⟶ W_{j,k}`, such that the composites `{T_{j,k} ⟶ S}` form an fppf covering
refining `𝒮`.

This is `exists_openCover_finiteLocallyFree_refinement_of_hasQuasiFiniteSlices` applied to
`AlgebraicGeometry.hasQuasiFiniteSlices`, the form of [Stacks, Tag 0570] used here. -/
@[stacks 05WN]
theorem exists_openCover_finiteLocallyFree_refinement (S : Scheme.{u})
    (𝒮 : S.Cover.{v} Scheme.fppfPrecoverage) :
    ∃ (𝒰 : S.OpenCover.{max u v})
      (W : 𝒰.I₀ → Scheme.{u})
      (g : ∀ j, W j ⟶ 𝒰.X j)
      (𝒲 : ∀ j, (W j).OpenCover.{max u v})
      (T : ∀ j, (𝒲 j).I₀ → Scheme.{u})
      (h : ∀ j k, T j k ⟶ (𝒲 j).X k),
      (∀ j, Surjective (g j) ∧ Stacks.Morphisms.IsFiniteLocallyFree (g j)) ∧
      (∀ j k, Surjective (h j k) ∧ Stacks.Morphisms.IsFiniteLocallyFree (h j k)) ∧
      Presieve.ofArrows
          (fun jk : Σ j, (𝒲 j).I₀ ↦ T jk.1 jk.2)
          (fun jk ↦ h jk.1 jk.2 ≫ (𝒲 jk.1).f jk.2 ≫ g jk.1 ≫ 𝒰.f jk.1) ∈
        Scheme.fppfPrecoverage S ∧
      ∀ j k, ∃ i, ∃ l : T j k ⟶ 𝒮.X i,
        l ≫ 𝒮.f i = h j k ≫ (𝒲 j).f k ≫ g j ≫ 𝒰.f j :=
  exists_openCover_finiteLocallyFree_refinement_of_hasQuasiFiniteSlices hasQuasiFiniteSlices S 𝒮

end Stacks.Topologies.Fppf

end
