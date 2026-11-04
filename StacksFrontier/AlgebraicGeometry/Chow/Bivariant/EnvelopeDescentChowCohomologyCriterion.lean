module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting

/-!
# Descent of Chow cohomology classes along an envelope, for a natural Gysin system

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `g : Y ⟶ X` be an envelope (Stacks 0GU5) and let
`a, b : Y ×_X Y ⟶ Y` be the two projections. A class `d ∈ A^p(Y)` with

  `res_a(d) = res_b(d)`  in  `A^p(Y ×_X Y)`

is `res(c)` for a unique `c ∈ A^p(X)`, where `res` is the restriction map of Stacks 0B7F,
`Stacks.Chow.chowCohomologyRestriction`. This is Stacks 0GUC for the identity of `X`, read on
the restriction map of Chow cohomology. Bivariant classes are taken against an arbitrary
`Stacks.Chow.GysinSystem` having the three naturality properties that the descent statement
`Stacks.Chow.existsUnique_bivariantRestriction_eq_of_naturality` uses; for the Gysin system of the
first Chern class of an invertible module this is
`Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_of_isEnvelope`.

## Main definitions

* `Stacks.Chow.chowCohomologyDescentClass` — a Chow cohomology class of `Y`, read as a bivariant
  class for the base change `X ×_X Y ⟶ Y` of the identity of `X`; the input of Stacks 0GUC.

## Main results

* `Stacks.Chow.chowCohomologyRestriction_eq_iff_bivariantRestriction_eq` — `res(c) = d` exactly
  when the restriction of Stacks 0F9Z of `c` along `g` is the class attached to `d`.
* `Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_of_naturality` — the descent, with the
  descent condition read on the operations of `d` on the test schemes over `Y ×_X Y`.
* `Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_of_restriction_eq` — the descent, with
  the descent condition the equality `res_a(d) = res_b(d)`.

## Implementation notes

The two projections satisfy `a ≫ g = b ≫ g`, so the structure morphisms `a ≫ (g ≫ sX)` and
`b ≫ (g ≫ sX)` of `Y ×_X Y` are equal but not the same term; the equality `res_a(d) = res_b(d)`
is stated through the transport `Stacks.Chow.bivariantClassCongrBase` along it.

## References

* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0GU5](https://stacks.math.columbia.edu/tag/0GU5)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The operation of a restricted or transported Chow cohomology class -/

section IdRule

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Y : Scheme.{u}} (s : Y ⟶ C.S)
  [LocallyOfFiniteType s] (p : ℤ) (hgys : G.IsNaturalUnderBaseChangeIso)

/-- The restriction of a Chow cohomology class is the transport of its bivariant restriction. -/
private theorem chowCohomologyRestriction_eq_bivariantTransport
    (d : chowCohomologyComponent C G s p) {Z : Scheme.{u}} (a : Z ⟶ Y) [LocallyOfFiniteType a] :
    chowCohomologyRestriction C G s a p hgys d =
      bivariantTransport C G (pullback.fst (𝟙 Y) a ≫ s) (a ≫ s) (a ≫ s) (pullback.snd (𝟙 Y) a)
        (pullbackSnd_comp_structureMorphism_eq C s s (𝟙 Y) (Category.id_comp s) a) (𝟙 Z)
        (Category.id_comp (a ≫ s)) (identityBaseChangeIso a) (by simp) p hgys
        (bivariantRestriction C G s s (𝟙 Y) (Category.id_comp s) a p hgys d) :=
  rfl

/-- **The operation of a restriction.** The operation of `res_a(d)` (Stacks 0B7F) on a test
scheme `t : T ⟶ Z` is the operation of `d` on `t ≫ a`. For the Gysin system of the first Chern
class of an invertible module this is
`Stacks.Chow.BivariantClass.idRule_chowCohomologyRestriction_heq`. -/
theorem chowCohomologyRestriction_idRule_heq (d : chowCohomologyComponent C G s p)
    {Z : Scheme.{u}} (a : Z ⟶ Y) [LocallyOfFiniteType a] {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ (a ≫ s)) k)
    (α' : chowGroup C ((t ≫ a) ≫ s) k) (hα : α ≍ α') :
    (chowCohomologyRestriction C G s a p hgys d).idRule C (a ≫ s) G t k α ≍
      d.idRule C s G (t ≫ a) k α' := by
  rw [← BivariantClass.isoCap_id, chowCohomologyRestriction_eq_bivariantTransport,
    BivariantClass.isoCap_bivariantTransport]
  exact BivariantClass.isoCap_bivariantRestriction_heq C G s s (𝟙 Y) (Category.id_comp s) a hgys
    d t k α α' hα

/-- The operation of the transport of a Chow cohomology class along an equality of structure
morphisms is the operation of the class. -/
theorem idRule_bivariantClassCongrBase_heq {s' : Y ⟶ C.S} [LocallyOfFiniteType s'] (hs : s = s')
    (c : chowCohomologyComponent C G s p) {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ s') k) (α' : chowGroup C (t ≫ s) k) (hα : α ≍ α') :
    (bivariantClassCongrBase C G (𝟙 Y) hs hs (hv := Category.id_comp s)
          (hv' := Category.id_comp s') p c).idRule C s' G t k α ≍
      c.idRule C s G t k α' := by
  subst hs
  cases hα
  rfl

end IdRule

/-! ### Descent of Chow cohomology classes -/

section Descent

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (g : Y ⟶ X) [LocallyOfFiniteType g] (p : ℤ)
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- A Chow cohomology class `d ∈ A^p(Y)` read as a bivariant class for the base change
`X ×_X Y ⟶ Y` of the identity of `X` along `g : Y ⟶ X`: its transport along the canonical
isomorphism `Y ≅ X ×_X Y`. This is the input of Stacks 0GUC for the identity of `X`. -/
def chowCohomologyDescentClass (d : chowCohomologyComponent C G (g ≫ sX) p) :
    BivariantClass C G (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) (pullback.snd (𝟙 X) g)
      (pullbackSnd_comp_structureMorphism_eq C sX sX (𝟙 X) (Category.id_comp sX) g) p :=
  bivariantTransport C G (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) (𝟙 Y)
    (Category.id_comp _) (pullback.snd (𝟙 X) g)
    (pullbackSnd_comp_structureMorphism_eq C sX sX (𝟙 X) (Category.id_comp sX) g)
    (identityBaseChangeIso g).symm (by simp) p hgys d

/-- For the Gysin system of the first Chern class of an invertible module,
`Stacks.Chow.chowCohomologyDescentClass` is `Stacks.Chow.chowCohomologyDescentInput`. -/
theorem chowCohomologyDescentClass_gysinSystemOfInvertible
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) (g ≫ sX) p) :
    chowCohomologyDescentClass C (gysinSystemOfInvertible C) sX g p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d =
      chowCohomologyDescentInput C sX g p d :=
  rfl

/-- The operation of the descent class on a test scheme is that of the class itself. -/
theorem isoCap_chowCohomologyDescentClass (d : chowCohomologyComponent C G (g ≫ sX) p)
    {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ (g ≫ sX)) k) :
    (chowCohomologyDescentClass C G sX g p hgys d).isoCap C G
        (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) (pullback.snd (𝟙 X) g)
        (pullbackSnd_comp_structureMorphism_eq C sX sX (𝟙 X) (Category.id_comp sX) g) t k α =
      d.idRule C (g ≫ sX) G t k α :=
  BivariantClass.isoCap_bivariantTransport C _ _ _ _ _ _ _ _ _ _ _ d t k α

/-- `res(c) = d` exactly when the restriction of Stacks 0F9Z of `c` along `g` is the descent
class of `d`. -/
theorem chowCohomologyRestriction_eq_iff_bivariantRestriction_eq
    (c : chowCohomologyComponent C G sX p) (d : chowCohomologyComponent C G (g ≫ sX) p) :
    chowCohomologyRestriction C G sX g p hgys c = d ↔
      bivariantRestriction C G sX sX (𝟙 X) (Category.id_comp sX) g p hgys c =
        chowCohomologyDescentClass C G sX g p hgys d := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine BivariantClass.eq_of_isoCap_eq C _ _ _ _ _ fun t _ k α ↦ ?_
    rw [isoCap_chowCohomologyDescentClass, ← h, ← BivariantClass.isoCap_id]
    exact (BivariantClass.isoCap_bivariantTransport C _ _ _ _ _ _ _ _ _ _ hgys _ t k α).symm
  · refine BivariantClass.eq_of_isoCap_eq C _ _ _ _ _ fun t _ k α ↦ ?_
    rw [chowCohomologyRestriction_eq_bivariantTransport,
      BivariantClass.isoCap_bivariantTransport, h, isoCap_chowCohomologyDescentClass]
    rfl

/-- The first restriction of the descent class of `d`, in the descent condition of Stacks 0GUC,
operates on a test scheme `t : T ⟶ Y ×_X Y` as `d` does on `t ≫ pr₁`. -/
theorem isoCap_envelopeDescentRes₁_chowCohomologyDescentClass_heq [IsProper g]
    (d : chowCohomologyComponent C G (g ≫ sX) p) {T : Scheme.{u}}
    (t : T ⟶ pullback g g) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ (pullback.fst g g ≫ (g ≫ sX))) k)
    (α' : chowGroup C ((t ≫ pullback.fst g g) ≫ (g ≫ sX)) k) (hα : α ≍ α') :
    (envelopeDescentRes₁ C G sX sX (𝟙 X) (Category.id_comp sX) g p hgys
        (chowCohomologyDescentClass C G sX g p hgys d)).isoCap C G _ _
        (envelopeFibreSquareMap (𝟙 X) g)
        (envelopeFibreSquareMap_comp_structureMorphism C sX sX (𝟙 X) (Category.id_comp sX) g)
        t k α ≍
      d.idRule C (g ≫ sX) G (t ≫ pullback.fst g g) k α' := by
  unfold envelopeDescentRes₁
  rw [BivariantClass.isoCap_bivariantTransport]
  refine (BivariantClass.isoCap_bivariantRestriction_heq C _ _ _ _ _ _ _ _ t k α α' hα).trans ?_
  rw [isoCap_chowCohomologyDescentClass]

/-- The second restriction of the descent class of `d`, in the descent condition of Stacks 0GUC,
operates on a test scheme `t : T ⟶ Y ×_X Y` as `d` does on `t ≫ pr₂`. -/
theorem isoCap_envelopeDescentRes₂_chowCohomologyDescentClass_heq [IsProper g]
    (d : chowCohomologyComponent C G (g ≫ sX) p) {T : Scheme.{u}}
    (t : T ⟶ pullback g g) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ (pullback.fst g g ≫ (g ≫ sX))) k)
    (α' : chowGroup C ((t ≫ pullback.snd g g) ≫ (g ≫ sX)) k) (hα : α ≍ α') :
    (envelopeDescentRes₂ C G sX sX (𝟙 X) (Category.id_comp sX) g p hgys
        (chowCohomologyDescentClass C G sX g p hgys d)).isoCap C G _ _
        (envelopeFibreSquareMap (𝟙 X) g)
        (envelopeFibreSquareMap_comp_structureMorphism C sX sX (𝟙 X) (Category.id_comp sX) g)
        t k α ≍
      d.idRule C (g ≫ sX) G (t ≫ pullback.snd g g) k α' := by
  have hW : pullback.snd g g ≫ (g ≫ sX) = pullback.fst g g ≫ (g ≫ sX) := by
    rw [← pullback.condition_assoc]
  have hα'' : chowGroupCongr C (congrArg (t ≫ ·) hW.symm) k α ≍ α' :=
    (chowGroupCongr_heq C _ k α).trans hα
  unfold envelopeDescentRes₂
  refine (BivariantClass.isoCap_congrBase_heq C _ _ _ _ _ hW _ _ t k α _
    (chowGroupCongr_heq C (congrArg (t ≫ ·) hW.symm) k α).symm).trans ?_
  rw [BivariantClass.isoCap_bivariantTransport]
  refine (BivariantClass.isoCap_bivariantRestriction_heq C _ _ _ _ _ _ _ _ t k _ α' hα'').trans ?_
  rw [isoCap_chowCohomologyDescentClass]

/-- **Descent of Chow cohomology classes along an envelope, for a natural Gysin system.** Let
`g : Y ⟶ X` be an envelope and let `d ∈ A^p(Y)` be a class whose operations on `t ≫ pr₁` and
`t ≫ pr₂` agree for every test scheme `t : T ⟶ Y ×_X Y`. Then there is a unique `c ∈ A^p(X)`
whose restriction along `g` is `d`. This is Stacks 0GUC for the identity of `X`,
`Stacks.Chow.existsUnique_bivariantRestriction_eq_of_naturality`, read on Chow cohomology. -/
theorem existsUnique_chowCohomologyRestriction_eq_of_naturality
    (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysC : G.IsNaturalUnderPullbackCompPushforward) (hgE : IsEnvelope g)
    (d : chowCohomologyComponent C G (g ≫ sX) p)
    (hd : ∀ {T : Scheme.{u}} (t : T ⟶ pullback g g) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C ((t ≫ pullback.fst g g) ≫ (g ≫ sX)) k)
      (β : chowGroup C ((t ≫ pullback.snd g g) ≫ (g ≫ sX)) k), α ≍ β →
        d.idRule C (g ≫ sX) G (t ≫ pullback.fst g g) k α ≍
          d.idRule C (g ≫ sX) G (t ≫ pullback.snd g g) k β) :
    ∃! c : chowCohomologyComponent C G sX p, chowCohomologyRestriction C G sX g p hgys c = d := by
  let : IsProper g := hgE.isProper
  have hres : envelopeDescentRes₁ C G sX sX (𝟙 X) (Category.id_comp sX) g p hgys
        (chowCohomologyDescentClass C G sX g p hgys d) =
      envelopeDescentRes₂ C G sX sX (𝟙 X) (Category.id_comp sX) g p hgys
        (chowCohomologyDescentClass C G sX g p hgys d) := by
    refine BivariantClass.eq_of_isoCap_eq C _ _ _ _ _ fun t _ k α ↦ eq_of_heq ?_
    have hW : t ≫ (pullback.fst g g ≫ (g ≫ sX)) = (t ≫ pullback.snd g g) ≫ (g ≫ sX) := by
      rw [Category.assoc, ← pullback.condition_assoc]
    refine (isoCap_envelopeDescentRes₁_chowCohomologyDescentClass_heq C G sX g p hgys d t k α
      (chowGroupCongr C (Category.assoc _ _ _).symm k α) (chowGroupCongr_heq C _ k α).symm).trans
      ?_
    refine ((hd t k _ (chowGroupCongr C hW k α)
      ((chowGroupCongr_heq C _ k α).trans (chowGroupCongr_heq C _ k α).symm)).trans ?_)
    exact (isoCap_envelopeDescentRes₂_chowCohomologyDescentClass_heq C G sX g p hgys d t k α _
      (chowGroupCongr_heq C hW k α).symm).symm
  obtain ⟨c, hc, huniq⟩ := existsUnique_bivariantRestriction_eq_of_naturality C G sX sX (𝟙 X)
    (Category.id_comp sX) g p (chowCohomologyDescentClass C G sX g p hgys d) hgys hres hgE hgysP
    hgysC
  exact ⟨c, (chowCohomologyRestriction_eq_iff_bivariantRestriction_eq C G sX g p hgys c d).2 hc,
    fun e he ↦ huniq e ((chowCohomologyRestriction_eq_iff_bivariantRestriction_eq C G sX g p hgys
      e d).1 he)⟩

/-- The two projections of `Y ×_X Y` present the same structure morphism of `Y ×_X Y` over the
base. -/
theorem selfPullbackSnd_comp_structureMorphism_eq :
    pullback.snd g g ≫ (g ≫ sX) = pullback.fst g g ≫ (g ≫ sX) := by
  rw [← Category.assoc, ← Category.assoc, pullback.condition]

/-- **Descent of Chow cohomology classes along an envelope, from the equality of the two
restrictions.** Let `g : Y ⟶ X` be an envelope, let `a, b : Y ×_X Y ⟶ Y` be the two projections
and let `d ∈ A^p(Y)` satisfy `res_a(d) = res_b(d)`, the two sides compared in `A^p(Y ×_X Y)`
through the transport along the equality of the two presentations `a ≫ (g ≫ sX)` and
`b ≫ (g ≫ sX)` of the structure morphism of `Y ×_X Y`. Then there is a unique `c ∈ A^p(X)` with
`res(c) = d`. -/
theorem existsUnique_chowCohomologyRestriction_eq_of_restriction_eq
    (hgysP : G.IsNaturalUnderProperPushforward)
    (hgysC : G.IsNaturalUnderPullbackCompPushforward) (hgE : IsEnvelope g)
    (d : chowCohomologyComponent C G (g ≫ sX) p)
    (hd : chowCohomologyRestriction C G (g ≫ sX) (pullback.fst g g) p hgys d =
      bivariantClassCongrBase C G (𝟙 (pullback g g))
        (selfPullbackSnd_comp_structureMorphism_eq C sX g)
        (selfPullbackSnd_comp_structureMorphism_eq C sX g) (hv := Category.id_comp _)
        (hv' := Category.id_comp _) p
        (chowCohomologyRestriction C G (g ≫ sX) (pullback.snd g g) p hgys d)) :
    ∃! c : chowCohomologyComponent C G sX p, chowCohomologyRestriction C G sX g p hgys c = d := by
  refine existsUnique_chowCohomologyRestriction_eq_of_naturality C G sX g p hgys hgysP hgysC hgE d
    ?_
  intro T t _ k α β hαβ
  have h₁ : (t ≫ pullback.fst g g) ≫ (g ≫ sX) = t ≫ (pullback.fst g g ≫ (g ≫ sX)) :=
    Category.assoc _ _ _
  have h₂ : (t ≫ pullback.fst g g) ≫ (g ≫ sX) = t ≫ (pullback.snd g g ≫ (g ≫ sX)) := by
    rw [h₁, selfPullbackSnd_comp_structureMorphism_eq C sX g]
  refine (chowCohomologyRestriction_idRule_heq C G (g ≫ sX) p hgys d (pullback.fst g g) t k
    (chowGroupCongr C h₁ k α) α (chowGroupCongr_heq C h₁ k α)).symm.trans ?_
  rw [hd]
  refine (idRule_bivariantClassCongrBase_heq C G (pullback.snd g g ≫ (g ≫ sX)) p
    (selfPullbackSnd_comp_structureMorphism_eq C sX g) _ t k (chowGroupCongr C h₁ k α)
    (chowGroupCongr C h₂ k α)
    ((chowGroupCongr_heq C h₁ k α).trans (chowGroupCongr_heq C h₂ k α).symm)).trans ?_
  exact chowCohomologyRestriction_idRule_heq C G (g ≫ sX) p hgys d (pullback.snd g g) t k
    (chowGroupCongr C h₂ k α) β ((chowGroupCongr_heq C h₂ k α).trans hαβ)

end Descent

end Stacks.Chow

end
