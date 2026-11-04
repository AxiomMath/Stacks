module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteFreeDomination

/-!
# Zariski and finite locally free domination of an fppf covering

[Stacks, Tag 05WN] says that an fppf covering `{S_i → S}` is refined by a family built in four
steps: a Zariski open covering `S = ⋃ U_j`, surjective finite locally free `W_j → U_j`,
Zariski open coverings `W_j = ⋃_k W_{j,k}`, and surjective finite locally free
`T_{j,k} → W_{j,k}`.

It follows from [Stacks, Tag 0DET] — an fppf covering is refined by composites of an étale
covering with surjective finite locally free morphisms — and [Stacks, Tag 02LI]
(`Stacks.Topologies.Etale.exists_zariski_finiteLocallyFree_refinement`). Here Tag 0DET for the
given covering is the hypothesis `AlgebraicGeometry.EtaleFiniteLocallyFreeDominates`, so nothing
in this file is tagged; Tag 0DET itself is `Stacks.Topologies.Fppf.etaleFiniteLocallyFreeDominates`
and the unconditional, tagged form of Tag 05WN is
`Stacks.Topologies.Fppf.exists_openCover_finiteLocallyFree_refinement`.

## Main definitions

* `AlgebraicGeometry.EtaleFiniteLocallyFreeDominates` is the statement of [Stacks, Tag 0DET]
  for a single fppf covering.

## Main results

* `Stacks.Topologies.Fppf.exists_openCover_finiteLocallyFree_refinement_of_etaleDominates` is
  [Stacks, Tag 05WN], granted that hypothesis.

## Implementation notes

The hypothesis is phrased for the *given* covering rather than as a universally quantified
`Prop`, which is the weakest form that suffices and avoids fixing the index universe of the
dominating family.

The outer and inner Zariski coverings produced by Tag 02LI are indexed in `Type u`, while the
conclusion asks for coverings indexed in `Type (max u v)`; `Stacks.Topologies.Fppf.liftOpenCover`
reindexes an open covering along `ULift`.

## References

* [Stacks Project, Tag 05WN](https://stacks.math.columbia.edu/tag/05WN)
* [Stacks Project, Tag 0DET](https://stacks.math.columbia.edu/tag/0DET)
* [Stacks Project, Tag 02LI](https://stacks.math.columbia.edu/tag/02LI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- **The statement of [Stacks, Tag 0DET]** for a single fppf covering `𝒮` of `S`: there are an
étale covering `𝒱` of `S` and an fppf covering `𝒲` refining `𝒮`, indexed by the same type, with
each member of `𝒲` surjective and finite locally free over the corresponding member of `𝒱`. -/
def EtaleFiniteLocallyFreeDominates {S : Scheme.{u}} (𝒮 : S.Cover.{v} Scheme.fppfPrecoverage) :
    Prop :=
  ∃ (𝒱 : S.Cover.{u} Scheme.etalePrecoverage) (𝒲 : S.Cover.{u} Scheme.fppfPrecoverage),
    Nonempty (𝒲.toPreZeroHypercover.Hom 𝒮.toPreZeroHypercover) ∧
      ∃ (e : 𝒲.I₀ ≃ 𝒱.I₀) (g : ∀ a, 𝒲.X a ⟶ 𝒱.X (e a)),
        (∀ a, g a ≫ 𝒱.f (e a) = 𝒲.f a) ∧ (∀ a, Surjective (g a)) ∧
          ∀ a, Stacks.Morphisms.IsFiniteLocallyFree (g a)

end AlgebraicGeometry

namespace Stacks.Topologies.Fppf

private lemma eqToHom_comp_family {I : Type*} {S : Scheme.{u}} (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ S) {i j : I} (h : i = j) : eqToHom (congrArg X h) ≫ f j = f i := by
  cases h
  simp

/-- Reindex an open covering along `ULift`, to raise its index universe. -/
private def liftOpenCover {S : Scheme.{u}} (𝒰 : S.OpenCover.{u}) : S.OpenCover.{max u v} where
  I₀ := ULift.{max u v} 𝒰.I₀
  X j := 𝒰.X j.down
  f j := 𝒰.f j.down
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun j ↦ 𝒰.map_prop j.down⟩
    obtain ⟨j, y, hy⟩ := 𝒰.exists_eq x
    exact ⟨ULift.up j, y, hy⟩

/-- **Stacks Project, Tag 05WN**, granted [Stacks, Tag 0DET] for the given covering. Every fppf
covering is refined by a family obtained by successively taking a Zariski open cover, a
surjective finite locally free morphism, another Zariski open cover, and another surjective
finite locally free morphism. -/
theorem exists_openCover_finiteLocallyFree_refinement_of_etaleDominates
    (S : Scheme.{u}) (𝒮 : S.Cover.{v} Scheme.fppfPrecoverage)
    (hdet : EtaleFiniteLocallyFreeDominates 𝒮) :
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
        l ≫ 𝒮.f i = h j k ≫ (𝒲 j).f k ≫ g j ≫ 𝒰.f j := by
  obtain ⟨𝒱, 𝒵, ⟨href⟩, e, q, hqcomm, hqsurj, hqflf⟩ := hdet
  obtain ⟨𝒰, W, g, hgflf, hgsurj, 𝒲, ⟨r⟩⟩ :=
    Stacks.Topologies.Etale.exists_zariski_finiteLocallyFree_refinement
      𝒱.toPreZeroHypercover 𝒱.mem₀
  let E := 𝒰.toPreZeroHypercover.bind fun i ↦ (𝒲 i).toPreZeroHypercover.pushforward (g i)
  let idx : ∀ j, (𝒲 j).I₀ → E.I₀ := fun j k ↦ ⟨j, k⟩
  have hX : ∀ j k, E.X (idx j k) = (𝒲 j).X k := fun _ _ ↦ rfl
  let a : ∀ j, (𝒲 j).I₀ → 𝒵.I₀ := fun j k ↦ e.symm (r.s₀ (idx j k))
  have ha (j : 𝒰.I₀) (k : (𝒲 j).I₀) : e (a j k) = r.s₀ (idx j k) := e.apply_symm_apply _
  let rho : ∀ j k, (𝒲 j).X k ⟶ 𝒱.X (e (a j k)) := fun j k ↦
    eqToHom (hX j k).symm ≫ r.h₀ (idx j k) ≫ eqToHom (congrArg 𝒱.X (ha j k).symm)
  have hE (j : 𝒰.I₀) (k : (𝒲 j).I₀) :
      eqToHom (hX j k).symm ≫ E.f (idx j k) = (𝒲 j).f k ≫ g j ≫ 𝒰.f j := by
    cases hX j k
    simp only [E, idx, PreZeroHypercover.bind_f, PreZeroHypercover.pushforward_f]
    cat_disch
  have hρ (j : 𝒰.I₀) (k : (𝒲 j).I₀) :
      rho j k ≫ 𝒱.f (e (a j k)) = (𝒲 j).f k ≫ g j ≫ 𝒰.f j := by
    rw [← hE j k, ← r.w₀ (idx j k)]
    simp [rho, eqToHom_comp_family 𝒱.X 𝒱.f (ha j k).symm]
  let 𝒰' : S.OpenCover.{max u v} := liftOpenCover 𝒰
  let W' : 𝒰'.I₀ → Scheme.{u} := fun j ↦ W j.down
  let g' : ∀ j, W' j ⟶ 𝒰'.X j := fun j ↦ g j.down
  let 𝒲' : ∀ j, (W' j).OpenCover.{max u v} := fun j ↦ liftOpenCover (𝒲 j.down)
  let T : ∀ j, (𝒲 j).I₀ → Scheme.{u} := fun j k ↦ pullback (rho j k) (q (a j k))
  let h : ∀ j k, T j k ⟶ (𝒲 j).X k := fun j k ↦ pullback.fst (rho j k) (q (a j k))
  let T' : ∀ j, (𝒲' j).I₀ → Scheme.{u} := fun j k ↦ T j.down k.down
  let h' : ∀ j k, T' j k ⟶ (𝒲' j).X k := fun j k ↦ h j.down k.down
  have hh (j : 𝒰'.I₀) (k : (𝒲' j).I₀) :
      Surjective (h' j k) ∧ Stacks.Morphisms.IsFiniteLocallyFree (h' j k) :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback _ _).flip (hqsurj (a j.down k.down)),
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback _ _).flip (hqflf (a j.down k.down))⟩
  refine ⟨𝒰', W', g', 𝒲', T', h', fun j ↦ ⟨hgsurj j.down, hgflf j.down⟩, hh, ?_, ?_⟩
  · show Presieve.ofArrows (fun jk : Σ j, (𝒲' j).I₀ ↦ T' jk.1 jk.2)
        (fun jk ↦ h' jk.1 jk.2 ≫ (𝒲' jk.1).f jk.2 ≫ g' jk.1 ≫ 𝒰'.f jk.1) ∈
      Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) S
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun jk ↦ ?_⟩
    · obtain ⟨j, y, hy⟩ := 𝒰'.exists_eq x
      have : Surjective (g' j) := hgsurj j.down
      obtain ⟨y₁, hy₁⟩ := (g' j).surjective y
      obtain ⟨k, z, hz⟩ := (𝒲' j).exists_eq y₁
      have := (hh j k).1
      obtain ⟨z₁, hz₁⟩ := (h' j k).surjective z
      refine ⟨⟨j, k⟩, z₁, ?_⟩
      simp only [Scheme.Hom.comp_apply]
      rw [hz₁, hz, hy₁, hy]
    · have := (hh jk.1 jk.2).2
      have : Stacks.Morphisms.IsFiniteLocallyFree (g' jk.1) := hgflf jk.1.down
      have := Stacks.Morphisms.IsFiniteLocallyFree.flat (h' jk.1 jk.2)
      have := Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation (h' jk.1 jk.2)
      have := Stacks.Morphisms.IsFiniteLocallyFree.flat (g' jk.1)
      have := Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation (g' jk.1)
      exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨j⟩ ⟨k⟩
    refine ⟨href.s₀ (a j k), pullback.snd (rho j k) (q (a j k)) ≫ href.h₀ (a j k), ?_⟩
    rw [Category.assoc, href.w₀, ← hqcomm, ← Category.assoc, ← pullback.condition, Category.assoc,
      hρ]
    rfl

end Stacks.Topologies.Fppf

end
