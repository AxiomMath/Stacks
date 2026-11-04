module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf

/-!
# Stacks in groupoids are the stacks with groupoid fibres

Let `(𝒞, J)` be a site and let `p : 𝒮 ⥤ 𝒞` be a category over `𝒞`. A *stack in groupoids* over
`𝒞` (Stacks 02ZI) is a category over `𝒞` which is fibred in groupoids, whose presheaves
`Isom(x, y)` on `𝒞/U` are sheaves, and relative to which every descent datum for a covering is
effective. Stacks 02ZJ says that this is the same condition on `p` as being a stack over `𝒞`
whose fibre categories are all groupoids, and the same as being fibred in groupoids and a stack
over `𝒞`. Its content is the characterisation of categories fibred in groupoids as the fibred
categories with groupoid fibres (Stacks 003V,
`CategoryTheory.Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid`), together with
the fact that over a category fibred in groupoids `Isom(x, y)` is all of `Mor(x, y)`, every
morphism of a fibre being invertible.

## Main results

* `CategoryTheory.Functor.stackInGroupoids_tfae`: Stacks 02ZJ, the equivalence of the three
  conditions above.

## Implementation notes

The three conditions of Stacks 02ZI are spelled out in the first clause rather than referred to
`CategoryTheory.Functor.IsStackInGroupoids`, and they are spelled out in the language in which
`CategoryTheory.Functor.IsStack` (Stacks 026F) states the conditions of a stack: over covering
*sieves*, with the chosen pullbacks of the fibred structure that the first condition of 02ZI
provides. `IsStackInGroupoids` instead quantifies over covering *families* together with supplied
genuine fibre products `Vᵢ ×_U Vⱼ` and `Vᵢ ×_U Vⱼ ×_U Vₖ` for their overlaps, so over a base in
which those fibre products do not exist its conditions (2) and (3) are satisfied with nothing to
prove; it is therefore implied by the first clause below (this is
`CategoryTheory.Functor.IsStack.isStackInGroupoids`) but does not imply it. No such gap arises for
the source, whose sites have the fibre products of a covering by Sites, Definition 00VH (3);
Mathlib's `GrothendieckTopology` carries no such condition, and the clause below is stated so that
the equivalence holds over every Grothendieck topology.

Condition (2) of 02ZI is the sheaf condition for `Isom(x, y)`
(`CategoryTheory.Functor.isomPresheaf`), not for `Mor(x, y)`, so the first clause is not the third
clause unbundled: passing from one to the other is where the invertibility of the morphisms of a
fibre is used. Condition (3) of 02ZI is the effectivity of descent data of 026F verbatim, the two
definitions of a descent datum being the same one.

Each clause is a condition on the same pair `(p, J)`: the topology is `J` in all three, and the
presheaves `Mor(x, y)` and `Isom(x, y)` of Stacks 02ZB are presheaves on the slice `𝒞/U` for the
induced topology `J.over U`, not on `𝒞`. The hypotheses are exactly that `𝒞` carries the topology
`J` and that `p` is a functor to `𝒞`, and each clause uses both; fibredness of `p` is asserted by
the clauses rather than assumed, as it must be for the statement to be about an arbitrary category
over `𝒞`. The presheaves of 02ZB are built from the chosen pullbacks of the fibred structure that
the clause containing them provides, so the comparison morphisms are pinned rather than merely
existing. The three clauses are simultaneously satisfiable: the identity functor `𝟭 𝒞` is fibred in
groupoids with one-object fibres and is a stack over any site.

## References

* [Stacks 02ZJ](https://stacks.math.columbia.edu/tag/02ZJ)
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- If every fibre of `p` is a groupoid then every section of `Mor(x, y)` is an isomorphism, so the
subpresheaf `Isom(x, y)` of Stacks 02ZB is the whole of `Mor(x, y)`. -/
private lemma isomSubpresheaf_eq_top (p : 𝒮 ⥤ 𝒞) [p.IsFibered]
    (hg : ∀ V : 𝒞, IsGroupoid (p.Fiber V)) {U : 𝒞} (x y : p.Fiber U) :
    p.isomSubpresheaf x y = ⊤ :=
  le_antisymm le_top fun g m _ => by
    have := hg g.unop.left
    rw [mem_isomSubpresheaf_obj]
    infer_instance

/-- If every fibre of `p` is a groupoid then `Isom(x, y)` is a sheaf exactly when `Mor(x, y)` is:
the two presheaves are isomorphic by `CategoryTheory.Functor.isomSubpresheaf_eq_top`, and being a
sheaf is invariant under isomorphism of presheaves. This is the only point at which the conditions
of Stacks 02ZI and of Stacks 026F differ. -/
private lemma isSheaf_isomPresheaf_iff (p : 𝒮 ⥤ 𝒞) [p.IsFibered]
    (hg : ∀ V : 𝒞, IsGroupoid (p.Fiber V)) (J : GrothendieckTopology 𝒞) (U : 𝒞)
    (x y : p.Fiber U) :
    Presheaf.IsSheaf (J.over U) (p.isomPresheaf x y) ↔ IsMorSheaf p J U x y := by
  have hι : IsIso (p.isomSubpresheaf x y).ι :=
    (p.isomSubpresheaf x y).eq_top_iff_isIso.1 (isomSubpresheaf_eq_top p hg x y)
  have e : (p.isomSubpresheaf x y).toFunctor ≅ p.morPresheaf x y := @asIso _ _ _ _ _ hι
  exact Presheaf.isSheaf_of_iso_iff e

/-- **Stacks 02ZJ.** Let `(𝒞, J)` be a site and let `p : 𝒮 ⥤ 𝒞` be a category over `𝒞`. The
following are equivalent:
(1) `p` is a stack in groupoids over `𝒞`, that is `p` is fibred in groupoids, the presheaves
    `Isom(x, y)` on `𝒞/U` are sheaves, and every descent datum relative to a covering is
    effective (Stacks 02ZI);
(2) `p` is a stack over `𝒞` and all its fibre categories are groupoids;
(3) `p` is fibred in groupoids over `𝒞` and is a stack over `𝒞`. -/
@[stacks 02ZJ]
public theorem stackInGroupoids_tfae (p : 𝒮 ⥤ 𝒞) (J : GrothendieckTopology 𝒞) :
    List.TFAE
      [ ∃ h : p.IsFiberedInGroupoids,
          haveI : p.IsFibered := h.isFibered
          (∀ (U : 𝒞) (x y : p.Fiber U),
              Presheaf.IsSheaf (J.over U) (p.isomPresheaf x y)) ∧ p.HasEffectiveDescent J,
        p.IsStack J ∧ ∀ U : 𝒞, IsGroupoid (p.Fiber U),
        p.IsFiberedInGroupoids ∧ p.IsStack J ] := by
  tfae_have 1 → 3 := by
    rintro ⟨h, hsheaf, hdesc⟩
    have hf : p.IsFibered := h.isFibered
    have hg : ∀ V : 𝒞, IsGroupoid (p.Fiber V) := h.fiber_isGroupoid
    exact ⟨h, { isFibered := hf
                isMorSheaf := fun U x y =>
                  (isSheaf_isomPresheaf_iff p hg J U x y).1 (hsheaf U x y)
                hasEffectiveDescent := hdesc }⟩
  tfae_have 3 → 2 := fun ⟨h, hs⟩ => ⟨hs, h.fiber_isGroupoid⟩
  tfae_have 2 → 1 := by
    rintro ⟨hs, hg⟩
    have hf : p.IsFibered := hs.isFibered
    refine ⟨IsFiberedInGroupoids.mk' hg, fun U x y => ?_, hs.hasEffectiveDescent⟩
    exact (isSheaf_isomPresheaf_iff p hg J U x y).2 (hs.isMorSheaf U x y)
  tfae_finish

end CategoryTheory.Functor
