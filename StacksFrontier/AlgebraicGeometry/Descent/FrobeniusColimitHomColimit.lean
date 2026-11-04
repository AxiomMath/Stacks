module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageShift

/-!
# The Hom-sets of the colimit category along an endofunctor are colimits

Let `F : C ⥤ C` be an endofunctor and let `colim_F C` be the colimit category of Stacks Tag
0EXA (`CategoryTheory.EndoColim`). The tag describes its Hom-sets as

`Hom((E, n), (G, m)) = colim_N Hom_C(F^{N - n}E, F^{N - m}G)`,

the colimit running over the integers `N ≥ n, m` along the maps `f ↦ F f`. This file states that
description as a theorem: the Hom-set of `colim_F C` is the colimit, in the category of types, of
the sequential diagram `N ↦ Hom_C(F^{N - n}E, F^{N - m}G)`, `N ≥ max(n, m)`.

## Main definitions

* `CategoryTheory.EndoColim.HomAt`: the Hom-set `Hom_C(F^{N - n}E, F^{N - m}G)` at the level
  `N = max(n, m) + k`.
* `CategoryTheory.EndoColim.homDiagram`: the sequential diagram of these Hom-sets, along the
  maps `f ↦ F^{k' - k} f`.
* `CategoryTheory.EndoColim.homCocone`: the cocone on it with summit `Hom((E, n), (G, m))`, whose
  leg at `N` takes a morphism of `C` to the morphism of `colim_F C` it presents.
* `CategoryTheory.EndoColim.homEquivColimit`: the bijection of `Hom((E, n), (G, m))` with the
  colimit of the diagram.

## Main results

* `CategoryTheory.EndoColim.homCoconeIsColimit`: **the Hom-set of `colim_F C` from `(E, n)` to
  `(G, m)` is the colimit `colim_N Hom_C(F^{N - n}E, F^{N - m}G)`**, the colimit maps being the
  presentations of morphisms.
* `CategoryTheory.EndoColim.homEquivColimit_homAtOf`: the bijection takes the morphism of
  `colim_F C` presented by a morphism of `C` at a level to the image of that morphism in the
  colimit.

## Implementation notes

The levels are indexed by `k : ℕ`, standing for the absolute level `N = max(n, m) + k`; these are
exactly the `N ≥ n, m`. The leg at `k` raises a morphism `F^{N - n}E ⟶ F^{N - m}G` by
`min(n, m)` and reads the result as a presentation at level `k` in the sense of
`CategoryTheory.EndoColim.HomRep` (whose levels are offset by `n + m` rather than by
`max(n, m)`). That this cocone is a colimit is
`CategoryTheory.Limits.Types.FilteredColimit.isColimitOf`: every morphism of `colim_F C` is
presented at some level (`CategoryTheory.EndoColim.Hom.exists_of`), and two presentations present
the same morphism exactly when they agree after raising
(`CategoryTheory.EndoColim.Hom.of_eq_of_iff`).

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.EndoColim

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

/-- The Hom-set `Hom_C(F^{N - n}E, F^{N - m}G)` at the absolute level `N = max(n, m) + k`, for the
objects `A = (E, n)` and `B = (G, m)` of `colim_F C`. -/
abbrev HomAt (A B : EndoColim F) (k : ℕ) : Type v :=
  (F.endoIter (max A.stage B.stage + k - A.stage)).obj A.obj ⟶
    (F.endoIter (max A.stage B.stage + k - B.stage)).obj B.obj

/-- The transition map of the diagram of Hom-sets from the level `k` to the level `k' ≥ k`: apply
`F^{k' - k}`. -/
def homAtMap (A B : EndoColim F) {k k' : ℕ} (h : k ≤ k') (f : HomAt A B k) : HomAt A B k' :=
  endoHomCast (by omega) (by omega) (endoRaise f (k' - k))

/-- The transition map of the diagram of Hom-sets from a level to itself is the identity. -/
lemma homAtMap_self (A B : EndoColim F) (k : ℕ) (f : HomAt A B k) :
    homAtMap A B (le_refl k) f = f :=
  endoHomCast_endoRaise_eq f (j' := 0) (Nat.sub_self k) _ _ rfl rfl

/-- The transition maps of the diagram of Hom-sets compose: going from `k` to `k'` and then to
`k''` is the transition map from `k` to `k''`. -/
lemma homAtMap_homAtMap (A B : EndoColim F) {k k' k'' : ℕ} (h : k ≤ k') (h' : k' ≤ k'')
    (f : HomAt A B k) :
    homAtMap A B h' (homAtMap A B h f) = homAtMap A B (h.trans h') f := by
  simp only [homAtMap, endoRaise_endoHomCast, endoRaise_endoRaise, endoHomCast_endoHomCast]
  exact endoHomCast_endoRaise_eq f (by omega) _ _ _ _

/-- **The diagram of Hom-sets** `N ↦ Hom_C(F^{N - n}E, F^{N - m}G)` over the levels
`N = max(n, m) + k ≥ n, m`, whose transition maps are `f ↦ F^{k' - k} f`. -/
def homDiagram (A B : EndoColim F) : ℕ ⥤ Type v where
  obj k := HomAt A B k
  map {k k'} h := TypeCat.ofHom (homAtMap A B (leOfHom h))
  map_id k := by
    ext f
    exact homAtMap_self A B k f
  map_comp {k k' k''} h h' := by
    ext f
    exact (homAtMap_homAtMap A B (leOfHom h) (leOfHom h') f).symm

/-- The map of the diagram of Hom-sets along `k ⟶ k'` is the transition map `homAtMap`. -/
@[simp]
lemma homDiagram_map_apply (A B : EndoColim F) {k k' : ℕ} (h : k ⟶ k') (f : HomAt A B k) :
    (homDiagram A B).map h f = homAtMap A B (leOfHom h) f :=
  rfl

/-- The morphism of `colim_F C` from `(E, n)` to `(G, m)` presented by a morphism
`F^{N - n}E ⟶ F^{N - m}G` of `C` at the absolute level `N = max(n, m) + k`. -/
def homAtOf (A B : EndoColim F) (k : ℕ) (f : HomAt A B k) : A ⟶ B :=
  Hom.of k (endoHomCast (by omega) (by omega) (endoRaise f (min A.stage B.stage)))

/-- **The presented morphism does not change along the transition maps of the diagram.** -/
lemma homAtOf_homAtMap (A B : EndoColim F) {k k' : ℕ} (h : k ≤ k') (f : HomAt A B k) :
    homAtOf A B k' (homAtMap A B h f) = homAtOf A B k f := by
  refine Hom.of_eq_of _ _ 0 (k' - k) (by omega) ?_
  simp only [homAtMap, endoRaise_zero, endoRaise_endoHomCast, endoRaise_endoRaise,
    endoHomCast_endoHomCast]
  exact endoHomCast_endoRaise_eq f (by omega) _ _ _ _

/-- The cocone on the diagram of Hom-sets with summit `Hom((E, n), (G, m))`, whose leg at a level
takes a morphism of `C` to the morphism of `colim_F C` it presents. -/
def homCocone (A B : EndoColim F) : Cocone (homDiagram A B) where
  pt := A ⟶ B
  ι :=
    { app k := TypeCat.ofHom (homAtOf A B k)
      naturality {k k'} h := by
        ext f
        exact homAtOf_homAtMap A B (leOfHom h) f }

/-- The leg of `homCocone` at the level `k` sends a morphism of `C` to the morphism `homAtOf`
of `colim_F C` it presents. -/
@[simp]
lemma homCocone_ι_app_apply (A B : EndoColim F) (k : ℕ) (f : HomAt A B k) :
    (homCocone A B).ι.app k f = homAtOf A B k f :=
  rfl

/-- Every morphism of `colim_F C` is presented at some level of the diagram of Hom-sets. -/
lemma exists_homAtOf (A B : EndoColim F) (u : A ⟶ B) :
    ∃ (k : ℕ) (f : HomAt A B k), homAtOf A B k f = u := by
  obtain ⟨l, g, rfl⟩ := Hom.exists_of u
  refine ⟨l + min A.stage B.stage, endoHomCast (by omega) (by omega) g, ?_⟩
  refine Eq.trans ?_ (Hom.of_raise l g (min A.stage B.stage))
  refine congrArg (Hom.of _) ?_
  rw [endoRaise_endoHomCast, endoHomCast_endoHomCast]

/-- Two morphisms of `C` at two levels which present the same morphism of `colim_F C` become
equal at some common higher level of the diagram of Hom-sets. -/
lemma exists_homAtMap_eq_of_homAtOf_eq (A B : EndoColim F) {i j : ℕ} (x : HomAt A B i)
    (y : HomAt A B j) (h : homAtOf A B i x = homAtOf A B j y) :
    ∃ (K : ℕ) (hi : i ≤ K) (hj : j ≤ K), homAtMap A B hi x = homAtMap A B hj y := by
  obtain ⟨a, b, hab, e⟩ := (Hom.of_eq_of_iff _ _).1 h
  dsimp only at hab e
  simp only [endoRaise_endoHomCast, endoRaise_endoRaise, endoHomCast_endoHomCast] at e
  refine ⟨i + a + min A.stage B.stage, by omega, by omega, ?_⟩
  have e' := congrArg (endoHomCast
    (m' := max A.stage B.stage + (i + a + min A.stage B.stage) - A.stage)
    (n' := max A.stage B.stage + (i + a + min A.stage B.stage) - B.stage)
    (by omega) (by omega)) e
  simp only [endoHomCast_endoHomCast] at e'
  simp only [homAtMap]
  refine Eq.trans ?_ (e'.trans ?_)
  · exact endoHomCast_endoRaise_eq x (by omega) _ _ _ _
  · exact endoHomCast_endoRaise_eq y (by omega) _ _ _ _

/-- **Stacks Tag 0EXA, the Hom-sets of `colim_F C`.** The Hom-set of `colim_F C` from `(E, n)` to
`(G, m)` is the colimit `colim_N Hom_C(F^{N - n}E, F^{N - m}G)` over the levels `N ≥ n, m`, along
the maps `f ↦ F f`, the colimit maps taking a morphism of `C` to the morphism of `colim_F C` it
presents. -/
noncomputable def homCoconeIsColimit (A B : EndoColim F) : IsColimit (homCocone A B) :=
  Types.FilteredColimit.isColimitOf _ _
    (fun u ↦ by
      obtain ⟨k, f, hf⟩ := exists_homAtOf A B u
      exact ⟨k, f, hf.symm⟩)
    (fun i j x y h ↦ by
      obtain ⟨K, hi, hj, e⟩ := exists_homAtMap_eq_of_homAtOf_eq A B x y h
      exact ⟨K, homOfLE hi, homOfLE hj, e⟩)

/-- The bijection of the Hom-set `Hom((E, n), (G, m))` of `colim_F C` with the colimit
`colim_N Hom_C(F^{N - n}E, F^{N - m}G)`. -/
noncomputable def homEquivColimit (A B : EndoColim F) :
    (A ⟶ B) ≃ colimit (homDiagram A B) :=
  ((homCoconeIsColimit A B).coconePointUniqueUpToIso (colimit.isColimit _)).toEquiv

/-- **The bijection takes the morphism presented by a morphism of `C` at a level to the image of
that morphism in the colimit.** -/
lemma homEquivColimit_homAtOf (A B : EndoColim F) (k : ℕ) (f : HomAt A B k) :
    homEquivColimit A B (homAtOf A B k f) = colimit.ι (homDiagram A B) k f :=
  congrArg (fun φ ↦ φ f)
    ((homCoconeIsColimit A B).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) k)

end CategoryTheory.EndoColim

end
