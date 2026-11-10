module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FiniteFreeDomination

/-!
# Étale-local finite locally free domination of an fppf covering

[Stacks, Tag 0DET] says that an fppf covering `{S_i → S}` is refined by a family
`{V_a → S}` in which each `V_a → S` factors as `V_a → S'_a → S` with `{S'_a → S}` étale and
`V_a → S'_a` surjective finite locally free.

The Stacks proof first replaces the covering by a locally quasi-finite one
([Stacks, Tag 0572]) and then applies the étale localization of quasi-finite morphisms
([Stacks, Tag 02LK], see `StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood`) at every
point. Here the first step is taken as the hypothesis
`AlgebraicGeometry.HasLocallyQuasiFiniteRefinement`, the statement of Tag 0572 for the given
covering. Together with
`Stacks.Topologies.Fppf.exists_openCover_finiteLocallyFree_refinement_of_etaleDominates` this
gives [Stacks, Tag 05WN] under the same hypothesis.

## Main definitions

* `AlgebraicGeometry.HasLocallyQuasiFiniteRefinement` is the statement of [Stacks, Tag 0572]
  for a single fppf covering.

## Main results

* `Stacks.Topologies.Fppf.etaleFiniteLocallyFreeDominates_of_hasLocallyQuasiFiniteRefinement`
  is [Stacks, Tag 0DET], granted that hypothesis.
* `Stacks.Topologies.Fppf.exists_openCover_finiteLocallyFree_refinement_of_locallyQuasiFinite`
  is [Stacks, Tag 05WN], granted that hypothesis.

## Implementation notes

The dominating étale covering is indexed by the total space `Σ j, 𝒵.X j` of the locally
quasi-finite refinement `𝒵`: at a point `x` of `𝒵.X j`, Tag 02LK supplies an elementary étale
neighbourhood `B` of the image of `x` and an open `V` of `𝒵.X j ×_S B` finite over `B`, which
is finite locally free by [Stacks, Tag 02KB] since it is also flat and locally of finite
presentation. Its image is open because flat and locally of finite presentation morphisms are
universally open, and restricting to that image makes it surjective.

## References

* [Stacks Project, Tag 0DET](https://stacks.math.columbia.edu/tag/0DET)
* [Stacks Project, Tag 0572](https://stacks.math.columbia.edu/tag/0572)
* [Stacks Project, Tag 02LK](https://stacks.math.columbia.edu/tag/02LK)
* [Stacks Project, Tag 05WN](https://stacks.math.columbia.edu/tag/05WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- **The statement of [Stacks, Tag 0572]** for a single fppf covering `𝒰` of `S`: there is an
fppf covering of `S` refining `𝒰` whose members are locally quasi-finite over `S`. -/
def HasLocallyQuasiFiniteRefinement {S : Scheme.{u}}
    (𝒰 : S.Cover.{v} Scheme.fppfPrecoverage) : Prop :=
  ∃ 𝒱 : S.Cover.{u} Scheme.fppfPrecoverage,
    Nonempty (𝒱.toPreZeroHypercover.Hom 𝒰.toPreZeroHypercover) ∧
      ∀ j, LocallyOfFiniteType (𝒱.f j) ∧ LocallyQuasiFinite (𝒱.f j)

end AlgebraicGeometry

namespace Stacks.Topologies.Fppf

/-- **Stacks Project, Tag 0DET**, granted [Stacks, Tag 0572] for the given covering. An fppf
covering is refined by composites of an étale covering with surjective finite locally free
morphisms. -/
theorem etaleFiniteLocallyFreeDominates_of_hasLocallyQuasiFiniteRefinement {S : Scheme.{u}}
    (𝒰 : S.Cover.{v} Scheme.fppfPrecoverage) (h𝒰 : HasLocallyQuasiFiniteRefinement 𝒰) :
    EtaleFiniteLocallyFreeDominates 𝒰 := by
  classical
  obtain ⟨𝒵, ⟨r⟩, hprops⟩ := h𝒰
  have hmap (k : 𝒵.I₀) : Flat (𝒵.f k) ∧ LocallyOfFinitePresentation (𝒵.f k) := by
    change (@Flat ⊓ @LocallyOfFinitePresentation) (𝒵.f k)
    exact 𝒵.map_prop k
  have : Scheme.JointlySurjective Scheme.fppfPrecoverage := by
    change Scheme.JointlySurjective (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
    infer_instance
  have hcover (s : S) : ∃ k, s ∈ Set.range (𝒵.f k) := by
    obtain ⟨k, x, hx⟩ := 𝒵.exists_eq s
    exact ⟨k, ⟨x, hx⟩⟩
  let I : Type u := Σ j, 𝒵.X j
  have hqf (a : I) : quasiFiniteAt (𝒵.f a.1) a.2 :=
    (forall_quasiFiniteAt_iff (𝒵.f a.1)).2 (hprops a.1) a.2
  let n : ∀ a : I, Stacks.Flatness.FiniteNeighborhoodAt (𝒵.f a.1) a.2 := fun a ↦
    have : LocallyOfFiniteType (𝒵.f a.1) := (hprops a.1).1
    Stacks.Flatness.finiteNeighborhoodAt (𝒵.f a.1) a.2
      (((quasiFiniteAt_tfae (𝒵.f a.1) a.2).out 1 2).mp (hqf a))
  let B (a : I) : Scheme.{u} := (n a).neighborhood.scheme
  let q (a : I) : B a ⟶ S := (n a).neighborhood.toBase
  let p (a : I) : ((n a).openSubscheme).toScheme ⟶ B a :=
    ((n a).openSubscheme).ι ≫ pullback.snd (𝒵.f a.1) ((n a).neighborhood.toBase)
  have hpflat (a : I) : Flat (p a) := by
    have := (hmap a.1).1
    infer_instance
  have hplfp (a : I) : LocallyOfFinitePresentation (p a) := by
    have := (hmap a.1).2
    infer_instance
  have hpflf (a : I) : Stacks.Morphisms.IsFiniteLocallyFree (p a) :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (p a)).2 ⟨(n a).spec.1, hpflat a, hplfp a⟩
  let O (a : I) : (B a).Opens :=
    have : UniversallyOpen (p a) := UniversallyOpen.of_flat (p a)
    ⟨Set.range (p a).base, (p a).isOpenMap.isOpen_range⟩
  let j (a : I) : (O a).toScheme ⟶ B a := (O a).ι
  let g (a : I) : pullback (p a) (j a) ⟶ (O a).toScheme := pullback.snd (p a) (j a)
  have hpt (a : I) : ∃ v, (p a) v = (n a).neighborhood.point := ((n a).spec.2.1).exists
  have hcoverV (s : S) : ∃ (a : I) (y : (O a).toScheme), (j a ≫ q a) y = s := by
    obtain ⟨k, x, hx⟩ := hcover s
    obtain ⟨v, hv⟩ := hpt ⟨k, x⟩
    exact ⟨⟨k, x⟩, ⟨(n ⟨k, x⟩).neighborhood.point, ⟨v, hv⟩⟩, by
      change (n ⟨k, x⟩).neighborhood.toBase (n ⟨k, x⟩).neighborhood.point = s
      rw [(n ⟨k, x⟩).neighborhood.map_point]; exact hx⟩
  let 𝒱 : S.Cover.{u} Scheme.etalePrecoverage :=
    Scheme.Cover.mkOfCovers (P := @Etale) I (fun a ↦ (O a).toScheme) (fun a ↦ j a ≫ q a)
      hcoverV
  have hgflf (a : I) : Stacks.Morphisms.IsFiniteLocallyFree (g a) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (p a) (j a)) (hpflf a)
  have hgsurj (a : I) : Surjective (g a) := by
    rw [AlgebraicGeometry.surjective_iff]
    intro y
    obtain ⟨x, hx⟩ : (j a).base y ∈ Set.range (p a).base := y.2
    obtain ⟨z, -, hz⟩ :=
      Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback (p a) (j a)) x y hx
    exact ⟨z, hz⟩
  let 𝒲 : S.Cover.{u} Scheme.fppfPrecoverage :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) I
      (fun a ↦ pullback (p a) (j a)) (fun a ↦ g a ≫ j a ≫ q a)
      (fun s ↦ by
        obtain ⟨a, y, hy⟩ := hcoverV s
        obtain ⟨z, hz⟩ := (AlgebraicGeometry.surjective_iff _).1 (hgsurj a) y
        exact ⟨a, z, by simpa [hz] using hy⟩)
      (map_prop := fun a ↦ by
        have hprops :=
          (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
            (g a)).mp (hgflf a)
        have : Flat (g a) := hprops.2.1
        have : LocallyOfFinitePresentation (g a) := hprops.2.2
        exact ⟨inferInstance, inferInstance⟩)
  refine ⟨𝒱, 𝒲, ⟨?_⟩, Equiv.refl I, g, fun a ↦ rfl, hgsurj, hgflf⟩
  exact { s₀ := fun a ↦ r.s₀ a.1
          h₀ := fun a ↦ pullback.fst (p a) (j a) ≫ ((n a).openSubscheme).ι ≫
            pullback.fst (𝒵.f a.1) ((n a).neighborhood.toBase) ≫ r.h₀ a.1
          w₀ := fun a ↦ by
            have hpull : pullback.fst (𝒵.f a.1) ((n a).neighborhood.toBase) ≫ 𝒵.f a.1 =
                pullback.snd (𝒵.f a.1) ((n a).neighborhood.toBase) ≫
                  (n a).neighborhood.toBase := pullback.condition
            have hpull' : pullback.fst (p a) (j a) ≫ p a =
                pullback.snd (p a) (j a) ≫ j a := pullback.condition
            calc
              ((pullback.fst (p a) (j a) ≫ ((n a).openSubscheme).ι ≫
                    pullback.fst (𝒵.f a.1) ((n a).neighborhood.toBase)) ≫ r.h₀ a.1) ≫
                  𝒰.f (r.s₀ a.1) =
                  (pullback.fst (p a) (j a) ≫ ((n a).openSubscheme).ι ≫
                    pullback.fst (𝒵.f a.1) ((n a).neighborhood.toBase)) ≫ 𝒵.f a.1 := by
                    rw [Category.assoc, r.w₀]
              _ = pullback.fst (p a) (j a) ≫ ((n a).openSubscheme).ι ≫
                    pullback.snd (𝒵.f a.1) ((n a).neighborhood.toBase) ≫
                    (n a).neighborhood.toBase := by
                    simpa only [Category.assoc] using
                      congrArg (fun t ↦ pullback.fst (p a) (j a) ≫
                        ((n a).openSubscheme).ι ≫ t) hpull
              _ = (pullback.fst (p a) (j a) ≫ p a) ≫ (n a).neighborhood.toBase := by
                    simp only [p, Category.assoc]
              _ = (pullback.snd (p a) (j a) ≫ j a) ≫ (n a).neighborhood.toBase := by
                    simpa only [Category.assoc] using
                      congrArg (fun t ↦ t ≫ (n a).neighborhood.toBase) hpull'
              _ = _ := by simp only [Category.assoc]; rfl }

/-- **Stacks Project, Tag 05WN**, granted [Stacks, Tag 0572] for the given covering: an fppf
covering is refined by a family obtained by successively taking a Zariski open cover, a
surjective finite locally free morphism, another Zariski open cover, and another surjective
finite locally free morphism. -/
theorem exists_openCover_finiteLocallyFree_refinement_of_locallyQuasiFinite
    (S : Scheme.{u}) (𝒮 : S.Cover.{v} Scheme.fppfPrecoverage)
    (h𝒮 : HasLocallyQuasiFiniteRefinement 𝒮) :
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
  exists_openCover_finiteLocallyFree_refinement_of_etaleDominates S 𝒮
    (etaleFiniteLocallyFreeDominates_of_hasLocallyQuasiFiniteRefinement 𝒮 h𝒮)

end Stacks.Topologies.Fppf

end
