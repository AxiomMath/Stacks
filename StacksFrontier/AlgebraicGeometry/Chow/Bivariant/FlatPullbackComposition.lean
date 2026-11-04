module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackNaturalityInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.AssociativityOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward

/-!
# The flat-pullback class of a composite is the composite of the flat-pullback classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` and
`g : Y ⟶ Z` be flat morphisms of relative dimensions `r` and `s` between schemes locally of finite
type over `S`. Then `f ≫ g` is flat of relative dimension `r + s` (Stacks 02NL), and the
flat-pullback classes of Stacks 0B78 satisfy

  `(g ∘ f)^* = f^* ∘ g^*` in `A^{-(r+s)}(X ⟶ Z)`.

This is Stacks 02RD read on bivariant classes. The two classes have degrees `-r + -s` and
`-(r + s)`, equal but not definitionally, so the equality is heterogeneous.

## Main results

* `Stacks.Chow.bivariantCompositeOfInvertible_flatPullbackBivariantClass` — the composite of the
  flat-pullback classes of `f` and `g`, at the Gysin system of the first Chern class rule with
  every input of Stacks 0B78 discharged, is the flat-pullback class of `f ≫ g`.

## References

* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 02NL](https://stacks.math.columbia.edu/tag/02NL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (g : Y ⟶ Z) [LocallyOfFiniteType g] [Flat g]
  (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (r s : ℕ)
  (hfr : AlgebraicGeometry.RelativeDimension f r) (hgs : AlgebraicGeometry.RelativeDimension g s)

/-- **Stacks 02RD, on bivariant classes.** For flat morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of
relative dimensions `r` and `s`, the composite `f^* ∘ g^*` of the flat-pullback classes of
Stacks 0B78 is the flat-pullback class `(g ∘ f)^*` of the composite, which is flat of relative
dimension `r + s`. The classes have degrees `-r + -s` and `-(r + s)`, whence the heterogeneous
equality. Every input of Stacks 0B78 is discharged. -/
theorem bivariantCompositeOfInvertible_flatPullbackBivariantClass :
    bivariantCompositeOfInvertible C sX sY sZ f g hf hg (-(r : ℤ)) (-(s : ℤ))
        (flatPullbackBivariantClassOfInvertible C sX sY f hf r hfr)
        (flatPullbackBivariantClassOfInvertible C sY sZ g hg s hgs) ≍
      flatPullbackBivariantClassOfInvertible C sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg)
          (r + s) (AlgebraicGeometry.RelativeDimension.comp_of_flat f g hfr hgs) := by
  refine BivariantClass.heq_of_congrHom_cap_heq rfl (by push_cast; ring) _ _ ?_
  intro T t _ k α
  have hfgS := comp_comp_structureMorphism_eq hf hg
  have hfg := AlgebraicGeometry.RelativeDimension.comp_of_flat f g hfr hgs
  set u := pullback.fst g t
  have hd : AlgebraicGeometry.RelativeDimension (pullback.snd f u ≫ pullback.snd g t) (r + s) :=
    AlgebraicGeometry.RelativeDimension.comp_of_flat _ _ (relativeDimension_pullbackSnd f hfr u)
      (relativeDimension_pullbackSnd g hgs t)
  have hbase : (pullback.snd f u ≫ pullback.snd g t) ≫ t ≫ sZ = pullback.fst f u ≫ sX := by
    rw [Category.assoc, ← pullback.condition_assoc, ← pullback.condition_assoc, hg, hf]
  have hL : (bivariantCompositeOfInvertible C sX sY sZ f g hf hg (-(r : ℤ)) (-(s : ℤ))
      (flatPullbackBivariantClassOfInvertible C sX sY f hf r hfr)
      (flatPullbackBivariantClassOfInvertible C sY sZ g hg s hgs)).cap t k α ≍
      chowPushforwardOfIso C (pullback.fst f u ≫ sX) (pullback.fst (f ≫ g) t ≫ sX)
        (pullbackRightPullbackFstIso g t f).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t) (k + ((r + s : ℕ) : ℤ))
        (flatPullbackChow C (pullback.fst f u ≫ sX) (t ≫ sZ)
          (pullback.snd f u ≫ pullback.snd g t) hbase
          (r + s) hd k (flatPullbackDescends C _ _ _ _ _ _ _) α) := by
    rw [bivariantCompositeOfInvertible, bivariantComposite_cap, bivariantCompositeCap_apply]
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    refine chowPushforwardOfIso_heq_congr C _ _ _ _ (by push_cast; ring) _ _ ?_
    refine (flatPullbackBivariantCap_heq C sX sY f hf r hfr (flatPullbackDescends C) u
      (k - -(s : ℤ)) _).trans ?_
    refine (flatPullbackChow_heq_congr C _ _ (pullback.snd f u) (pullback.snd f u)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf u)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf u) rfl rfl
      (relativeDimension_pullback_snd f u r hfr) (relativeDimension_pullback_snd f u r hfr)
      (by ring) _ (flatPullbackDescends C _ _ _ _ _ _ _) _
      (flatPullbackChow C (pullback.fst g t ≫ sY) (t ≫ sZ) (pullback.snd g t)
        (pullbackSnd_comp_structureMorphism_eq C sY sZ g hg t) s
        (relativeDimension_pullback_snd g t s hgs) k (flatPullbackDescends C _ _ _ _ _ _ _) α)
      (flatPullbackBivariantCap_heq C sY sZ g hg s hgs (flatPullbackDescends C) t k α)).trans ?_
    exact flatPullbackChow_comp_heq C (flatPullbackDescends C) _ _ _ _ _ _ _ r s _ _ k α
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by push_cast; ring) _ _ hL).trans ?_
  rw [chowPushforwardOfIso_comp_apply]
  refine HEq.trans ?_ (flatPullbackBivariantCap_heq C sX sZ (f ≫ g)
    hfgS (r + s)
    hfg (flatPullbackDescends C) t k
    α).symm
  have hiso := flatPullbackChow_chowPushforwardOfIso C (t ≫ sZ) (pullback.fst f u ≫ sX) (t ≫ sZ)
    (pullback.fst (f ≫ g) t ≫ sX) (𝟙 T) (Category.id_comp _)
    ((pullbackRightPullbackFstIso g t f).hom ≫ (pullback.congrHom rfl rfl).hom) (by simp [u])
    (pullback.snd f u ≫ pullback.snd g t) hbase
    (pullback.snd (f ≫ g) t)
    (pullbackSnd_comp_structureMorphism hfgS t)
    (by simp [u]) (r + s) hd
    (relativeDimension_pullbackSnd (f ≫ g)
      hfg t) k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α
  rw [chowPushforwardOfIso_id] at hiso
  refine HEq.trans (heq_of_eq ?_) (heq_of_eq hiso.symm)
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ (by simp) _ _ _ _

end Stacks.Chow

end
