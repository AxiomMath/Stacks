module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SplitOverCard

/-!
# The number of sheets of a finite étale morphism

Étale-locally a finite étale morphism `U ⟶ X` of constant rank `d` is a disjoint union of exactly
`d` copies of the base: `AlgebraicGeometry.exists_smallEtaleArrows_cover_natCard` is
`AlgebraicGeometry.exists_smallEtaleArrows_cover` together with the count of the sheets, which
comes from `IsSplitOver.natCard_I_eq`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX) [IsFinite (B.inclusion.map U.obj.hom)]

/-- Étale-locally on `X`, the structure morphism of `U` is a finite disjoint union of
isomorphisms: every point of an étale object `V` over `X` has an étale neighbourhood `Q ⟶ V`
over which `U` is described by finitely many pairwise disjoint morphisms `Q ⟶ U` whose graphs
cover `Q ×_X U`. The neighbourhood is the one supplied by the sheet data of the finite étale
morphism `V ×_X U ⟶ V`, and the morphisms `Q ⟶ U` are its sheets read as `Q`-points of `U`.
When `U ⟶ X` is finite locally free of rank `d` there are exactly `d` of them. -/
public theorem exists_smallEtaleArrows_cover_natCard
    (V : SmallEtale B X hX) (x : V.obj.left.1) :
    ∃ (Q : SmallEtale B X hX) (q : Q ⟶ V),
      x ∈ Set.range (B.inclusion.map q.hom.left) ∧
      ∃ (ι : Type u) (_ : Finite ι) (φ : ι → (Q ⟶ U)),
        (∀ z : ((smallEtaleBaseChange B U.obj.hom).obj Q).obj.left.1,
            ∃ i, z ∈ Set.range (B.inclusion.map
              (smallEtaleLiftGraph B X hX U Q (φ i)).hom.left)) ∧
        Pairwise (fun i j => smallEtaleArrowsDisjoint B X hX U Q (φ i) (φ j)) ∧
        ∀ d : ℕ, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map U.obj.hom) d →
          Nat.card ι = d := by
  classical
  have hVU := (IsPullback.of_hasPullback V.obj.hom U.obj.hom).map B.inclusion
  have hfin : IsFinite (B.inclusion.map (pullback.fst V.obj.hom U.obj.hom)) :=
    MorphismProperty.of_isPullback hVU.flip inferInstance
  have hEt : Etale (B.inclusion.map (pullback.fst V.obj.hom U.obj.hom)) :=
    MorphismProperty.of_isPullback hVU.flip inferInstance
  obtain ⟨N, g, hg, hcN, n, hn, ⟨hsp⟩⟩ :=
    Stacks.Etale.exists_compactSpace_etale_isSplitOver
      (B.inclusion.map (pullback.fst V.obj.hom U.obj.hom)) x
  have := hg
  have := hcN
  have hN : B.Contains N :=
    (Scheme.size_le_of_locallyOfFiniteType g).trans_lt V.obj.left.property
  let q₀ : B.obj N hN ⟶ V.obj.left := ObjectProperty.homMk g
  let Q : SmallEtale B X hX :=
    ⟨Over.mk (q₀ ≫ V.obj.hom), by
      show Etale (g ≫ B.inclusion.map V.obj.hom)
      infer_instance⟩
  let q : Q ⟶ V := ObjectProperty.homMk (Over.homMk q₀ rfl)
  let α : pullback Q.obj.hom U.obj.hom ⟶ pullback V.obj.hom U.obj.hom :=
    pullback.lift (pullback.fst Q.obj.hom U.obj.hom ≫ q₀) (pullback.snd Q.obj.hom U.obj.hom)
      (by rw [Category.assoc]; exact pullback.condition)
  have hα₁ : α ≫ pullback.fst V.obj.hom U.obj.hom =
      pullback.fst Q.obj.hom U.obj.hom ≫ q₀ := pullback.lift_fst _ _ _
  have hα₂ : α ≫ pullback.snd V.obj.hom U.obj.hom =
      pullback.snd Q.obj.hom U.obj.hom := pullback.lift_snd _ _ _
  have hsqB : IsPullback α (pullback.fst Q.obj.hom U.obj.hom)
      (pullback.fst V.obj.hom U.obj.hom) q₀ := by
    refine IsPullback.of_right ?_ hα₁ (IsPullback.of_hasPullback V.obj.hom U.obj.hom).flip
    rw [hα₂]
    exact (IsPullback.of_hasPullback Q.obj.hom U.obj.hom).flip
  have hsq := hsqB.map B.inclusion
  let σ (i : hsp.I) := hsp.sectionOfIsPullback hsq i
  have hσfst (i : hsp.I) :
      σ i ≫ B.inclusion.map (pullback.fst Q.obj.hom U.obj.hom) = 𝟙 _ :=
    hsp.sectionOfIsPullback_comp_snd hsq i
  let σ' (i : hsp.I) : Q.obj.left ⟶ pullback Q.obj.hom U.obj.hom :=
    ObjectProperty.homMk (σ i)
  have hfst (i : hsp.I) : σ' i ≫ pullback.fst Q.obj.hom U.obj.hom = 𝟙 Q.obj.left := by
    apply B.inclusion.map_injective
    simp only [Functor.map_comp, CategoryTheory.Functor.map_id]
    exact hσfst i
  let φ (i : hsp.I) : Q ⟶ U := ObjectProperty.homMk (Over.homMk
    (σ' i ≫ pullback.snd Q.obj.hom U.obj.hom) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hfst i, Category.id_comp]))
  have hσsnd (i : hsp.I) : σ i ≫ B.inclusion.map (pullback.snd Q.obj.hom U.obj.hom) =
      B.inclusion.map (φ i).hom.left :=
    (Functor.map_comp B.inclusion (σ' i) (pullback.snd Q.obj.hom U.obj.hom)).symm
  have hsheet (i : hsp.I) :
      hsp.sheet i ≫ B.inclusion.map (pullback.snd V.obj.hom U.obj.hom) =
        σ i ≫ B.inclusion.map (pullback.snd Q.obj.hom U.obj.hom) := by
    rw [← hsp.sectionOfIsPullback_comp_fst hsq i, Category.assoc, ← Functor.map_comp, hα₂]
  refine ⟨Q, q, ⟨n, hn⟩, hsp.I, hsp.finite_I, φ, ?_, ?_, fun d hd ↦ ?_⟩
  · intro z
    obtain ⟨i, hi⟩ := hsp.exists_mem_range_sectionOfIsPullback hsq z
    refine ⟨i, ?_⟩
    rwa [map_smallEtaleLiftGraph_eq B X hX U Q (φ i) (σ i) (hσfst i) (hσsnd i)]
  · intro i j hij
    refine smallEtaleArrowsDisjoint_of_isEmpty B X hX U Q (φ i) (φ j) ?_
    intro Z c hcc
    refine isEmpty_of_sheet_comp_snd_eq B X hX U V hsp hij c ?_
    rwa [hsheet i, hsheet j, hσsnd i, hσsnd j]
  · have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (B.inclusion.map (pullback.fst V.obj.hom U.obj.hom)) d :=
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback hVU.flip
    exact hsp.natCard_I_eq n d

end AlgebraicGeometry

end
