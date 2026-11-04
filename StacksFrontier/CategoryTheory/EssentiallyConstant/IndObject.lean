module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute

/-!
# Essentially constant ind-objects

Let `M : I ⥤ C` be a diagram indexed by a filtered category `I`. Stacks 05PY
characterises when `M` is an *essentially constant ind-object*, i.e. when the
formal filtered colimit that `M` represents is already represented by a single
object `X` of `C`. Four descriptions are shown to agree:

1. `IsEssentiallyConstantInd M`: there are a cocone `t` with apex `X`, an index
   `i` and a morphism `r : X ⟶ M i` splitting the coprojection `c_i` (that is,
   `r ≫ c_i = 𝟙 X`) which is cofinal, in the sense that for every `j` some
   transition map out of `M j` factors as `c_j ≫ r` followed by a transition map
   out of `M i`.
2. `HasCoconeWithBijectiveHomComparison M`: there is a cocone `t` with apex `X`
   for which the canonical comparison map
   `homComparison : colim_i Mor(W, M_i) → Mor(W, X)` is bijective for every `W`.
3. `HasColimitWithBijectiveHomComparison M`: the same, for a cocone that is in
   addition a colimit cocone.
4. `HasCoreflectionWithBijectiveHomComparison M`: there are `X`, an index `i` and
   a morphism `r : X ⟶ M i` for which the map
   `homComparisonInv : Mor(W, X) → colim_j Mor(W, M_j)`, `h ↦ [h ≫ r]`, is
   bijective for every `W`.

The diagram of Hom-sets used in (2), (3), (4) is
`homDiagram M W = M ⋙ coyoneda.obj (op W) : I ⥤ Type v`.

In cases (2), (3), (4) the object `X` is moreover a value of the essentially constant system:
see `isEssentiallyConstantWith_of_bijective_homComparison` and
`isEssentiallyConstantWith_of_bijective_homComparisonInv`.

## Implementation notes

Condition (1) mentions no colimit, so `IsEssentiallyConstantWith` and `IsEssentiallyConstantInd`
are stated for an arbitrary index category `I : Type u'` with `Category.{v'} I`. From
`homDiagram` onwards the index category is small, `I : Type v` with `SmallCategory I`, so that the
colimit of `homDiagram M W` exists in `Type v`.

Condition (1) is phrased with a bare cocone rather than a colimit cocone. This is not a weakening:
by `IsEssentiallyConstantWith.isColimit` a cocone carrying such a witness is a colimit cocone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.EssentiallyConstantInd

universe v' u' v u

section ArbitraryIndex

variable {C : Type u} [Category.{v} C] {I : Type u'} [Category.{v'} I]

section Witness

variable {J : Type*} [Category J]

/-- `M` is essentially constant as an ind-object with value `t.pt`, with respect
to the cocone `t`, witnessed by an index `i` and a morphism `r : t.pt ⟶ M i`, if
`r` splits the coprojection `c_i` and is cofinal. -/
@[stacks_fixed 05PU "(1), filtered case, conditions (a) and (b) with value t.pt", sga "4 I 8.4.4"]
structure IsEssentiallyConstantWith (M : J ⥤ C) (t : Cocone M) (i : J)
    (r : t.pt ⟶ M.obj i) : Prop where
  /-- `c_i ∘ r = id_X`. -/
  retraction : r ≫ t.ι.app i = 𝟙 t.pt
  /-- For each `j`, the composite `M_j → X → M_i → M_k` is a transition map of the
  diagram for a suitable `k`. -/
  cofinal : ∀ j : J, ∃ (k : J) (σ : i ⟶ k) (τ : j ⟶ k),
      M.map τ = t.ι.app j ≫ r ≫ M.map σ

end Witness

/-- `M` is an *essentially constant ind-object* if there exist a cocone `t`, an
index `i`, and a morphism `r : t.pt ⟶ M i` witnessing it. -/
@[stacks 05PU "(1), filtered case: the predicate that M is essentially constant",
  sga "4 I 8.4.4",
  sga "4 I 8.7.1.7"]
def IsEssentiallyConstantInd (M : I ⥤ C) : Prop :=
  ∃ (t : Cocone M) (i : I) (r : t.pt ⟶ M.obj i), IsEssentiallyConstantWith M t i r

/-- A cocone carrying an essential-constancy witness is a colimit cocone. -/
@[sga "4 I 8.7.1.7" "partial"]
def IsEssentiallyConstantWith.isColimit {M : I ⥤ C} {t : Cocone M} {i : I}
    {r : t.pt ⟶ M.obj i} (hr : IsEssentiallyConstantWith M t i r) : IsColimit t where
  desc s := r ≫ s.ι.app i
  fac s j := by
    obtain ⟨k, σ, τ, hkτ⟩ := hr.cofinal j
    rw [← s.w τ, hkτ, ← s.w σ]
    simp only [Category.assoc]
  uniq s u hu := by
    rw [← Category.id_comp u, ← hr.retraction, Category.assoc, hu i]

end ArbitraryIndex

section SmallIndex

variable {C : Type u} [Category.{v} C] {I : Type v} [SmallCategory I]

/-- The diagram `i ↦ Mor(W, M_i)` in `Type v` obtained from `M` by applying the
covariant Hom-functor `coyoneda.obj (op W) = Mor(W, -)`. Its (filtered) colimit
in `Type v` always exists. -/
abbrev homDiagram (M : I ⥤ C) (W : C) : I ⥤ Type v := M ⋙ coyoneda.obj (op W)

/-- The comparison map out of the colimit of Hom-sets. Given a cocone `t = (X, {c_i})` for `M` and
an object `W`, the family of maps `g ↦ c_i ∘ g : Mor(W, M_i) → Mor(W, X)` is compatible with the
transition maps and induces the canonical map `colim_i Mor(W, M_i) → Mor(W, X)`, sending the class
of `g : W ⟶ M_i` to `g ≫ c_i = c_i ∘ g`. -/
noncomputable def homComparison (M : I ⥤ C) (t : Cocone M) (W : C) :
    colimit (homDiagram M W) ⟶ (W ⟶ t.pt) :=
  colimit.desc (homDiagram M W) ((Cocone.functoriality M (coyoneda.obj (op W))).obj t)

/-- The comparison map in the reverse direction. Given an object `X`, an index `i`, and a
morphism `r : X ⟶ M i`, the map `Mor(W, X) → colim_j Mor(W, M_j)` sends `h : W ⟶ X` to the class
of `r ∘ h = h ≫ r : W ⟶ M i`. -/
noncomputable def homComparisonInv (M : I ⥤ C) {X : C} {i : I} (r : X ⟶ M.obj i)
    (W : C) : (W ⟶ X) → colimit (homDiagram M W) :=
  fun h => colimit.ι (homDiagram M W) i (h ≫ r)

/-- There is a cocone `(X, {c_i})` for `M` such
that `homComparison` is bijective for every `W`. -/
@[sga "4 I 8.4.4", sga "4 I 8.7.1.7"]
def HasCoconeWithBijectiveHomComparison (M : I ⥤ C) : Prop :=
  ∃ t : Cocone M, ∀ W : C, Function.Bijective (homComparison M t W)

/-- The colimit `X = colim_i M_i` exists (a cocone
`t` together with `IsColimit t`) and `homComparison` is bijective for every
`W`. -/
@[sga "4 I 8.7.1.7"]
def HasColimitWithBijectiveHomComparison (M : I ⥤ C) : Prop :=
  ∃ (t : Cocone M) (_ : IsColimit t), ∀ W : C, Function.Bijective (homComparison M t W)

/-- There exist an object `X`, an index `i`, and a
morphism `r : X ⟶ M i` such that `homComparisonInv` is bijective for every
`W`. -/
@[sga "4 I 8.4.4", sga "4 I 8.7.1.7"]
def HasCoreflectionWithBijectiveHomComparison (M : I ⥤ C) : Prop :=
  ∃ (X : C) (i : I) (r : X ⟶ M.obj i), ∀ W : C, Function.Bijective (homComparisonInv M r W)

/-! ### Computation rules for the two comparison maps -/

/-- `homComparison` sends the class of `g : W ⟶ M_i` (at index `i`) to
`g ≫ c_i`. -/
theorem homComparison_ι (M : I ⥤ C) (t : Cocone M) (W : C) (i : I) (g : W ⟶ M.obj i) :
    (ConcreteCategory.hom (homComparison M t W))
        ((ConcreteCategory.hom (colimit.ι (homDiagram M W) i)) g)
      = g ≫ t.ι.app i :=
  colimit.ι_desc_apply ((Cocone.functoriality M (coyoneda.obj (op W))).obj t) i g

/-- `homComparisonInv` sends `h : W ⟶ X` to the class of `h ≫ r` at index `i`. -/
theorem homComparisonInv_apply (M : I ⥤ C) {X : C} {i : I} (r : X ⟶ M.obj i) (W : C)
    (h : W ⟶ X) :
    homComparisonInv M r W h
      = (ConcreteCategory.hom (colimit.ι (homDiagram M W) i)) (h ≫ r) := rfl

/-- The transition map of `homDiagram M W` along `φ : a ⟶ b` is post-composition
with `M.map φ` (the Hom-functor `Mor(W, -)` is covariant). -/
theorem homDiagram_map_apply (M : I ⥤ C) (W : C) {a b : I} (φ : a ⟶ b)
    (g : W ⟶ M.obj a) : (homDiagram M W).map φ g = g ≫ M.map φ := rfl

/-- Two classes in the filtered colimit of Hom-sets agree iff the representatives agree after
composing with transition maps. -/
private theorem colimit_ι_eq_iff [IsFiltered I] (M : I ⥤ C) (W : C) {a b : I} (g : W ⟶ M.obj a)
    (g' : W ⟶ M.obj b) :
    (ConcreteCategory.hom (colimit.ι (homDiagram M W) a)) g
        = (ConcreteCategory.hom (colimit.ι (homDiagram M W) b)) g' ↔
      ∃ (k : I) (σ : a ⟶ k) (τ : b ⟶ k), g ≫ M.map σ = g' ≫ M.map τ :=
  Types.FilteredColimit.colimit_eq_iff _

namespace IsEssentiallyConstantWith

variable {M : I ⥤ C} {t : Cocone M} {i : I} {r : t.pt ⟶ M.obj i}

/-- At an essential-constancy witness, `homComparison M t W` is a left inverse of
`homComparisonInv M r W`. -/
theorem homComparison_homComparisonInv (hr : IsEssentiallyConstantWith M t i r) (W : C)
    (h : W ⟶ t.pt) :
    ConcreteCategory.hom (homComparison M t W) (homComparisonInv M r W h) = h := by
  rw [homComparisonInv_apply, homComparison_ι, Category.assoc, hr.retraction, Category.comp_id]

/-- At an essential-constancy witness for a filtered index category, `homComparisonInv M r W` is a
left inverse of `homComparison M t W`. -/
theorem homComparisonInv_homComparison [IsFiltered I] (hr : IsEssentiallyConstantWith M t i r)
    (W : C) (x : colimit (homDiagram M W)) :
    homComparisonInv M r W (ConcreteCategory.hom (homComparison M t W) x) = x := by
  obtain ⟨j, g, rfl⟩ := Types.jointly_surjective' x
  obtain ⟨k, σ, τ, hkτ⟩ := hr.cofinal j
  rw [homComparison_ι, homComparisonInv_apply, colimit_ι_eq_iff]
  exact ⟨k, σ, τ, by simp only [hkτ, Category.assoc]⟩

/-- If `M` is a filtered diagram, essentially constant with witness `(t, i, r)`, then
`homComparison M t W` is bijective for every `W`, with inverse `homComparisonInv M r W`. -/
theorem bijective_homComparison [IsFiltered I] (hr : IsEssentiallyConstantWith M t i r)
    (W : C) : Function.Bijective (ConcreteCategory.hom (homComparison M t W)) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨homComparisonInv M r W, hr.homComparisonInv_homComparison W,
      hr.homComparison_homComparisonInv W⟩

/-- If `M` is a filtered diagram, essentially constant with witness `(t, i, r)`, then
`homComparisonInv M r W` is bijective for every `W`, with inverse `homComparison M t W`. -/
theorem bijective_homComparisonInv [IsFiltered I] (hr : IsEssentiallyConstantWith M t i r)
    (W : C) : Function.Bijective (homComparisonInv M r W) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨ConcreteCategory.hom (homComparison M t W), hr.homComparison_homComparisonInv W,
      hr.homComparisonInv_homComparison W⟩

end IsEssentiallyConstantWith

/-- If `homComparison M t W` is bijective for every `W`, then `M` is essentially constant as an
ind-object with value `t.pt`, with respect to the cocone `t`. -/
@[stacks 05PY]
theorem isEssentiallyConstantWith_of_bijective_homComparison (M : I ⥤ C) [IsFiltered I]
    (t : Cocone M) (h : ∀ W : C, Function.Bijective (homComparison M t W)) :
    ∃ (i : I) (r : t.pt ⟶ M.obj i), IsEssentiallyConstantWith M t i r := by
  obtain ⟨x, hx⟩ := (h t.pt).surjective (𝟙 t.pt)
  obtain ⟨i, r, rfl⟩ := Types.jointly_surjective' x
  rw [homComparison_ι] at hx
  refine ⟨i, r, hx, fun j => ?_⟩
  have heq : (ConcreteCategory.hom (colimit.ι (homDiagram M (M.obj j)) j)) (𝟙 (M.obj j))
      = (ConcreteCategory.hom (colimit.ι (homDiagram M (M.obj j)) i)) (t.ι.app j ≫ r) := by
    apply (h (M.obj j)).injective
    rw [homComparison_ι, homComparison_ι, Category.id_comp, Category.assoc, hx]
    exact (Category.comp_id _).symm
  obtain ⟨k, τ, σ, hkστ⟩ := (colimit_ι_eq_iff ..).1 heq
  refine ⟨k, σ, τ, ?_⟩
  simp only [Category.id_comp, Category.assoc] at hkστ ⊢
  rw [hkστ]

/-- If `homComparisonInv M r W` is bijective for every `W`, for a morphism `r : X ⟶ M i`, then
`X` is the apex of a cocone with respect to which `M` is essentially constant, so `X` is a value of
the essentially constant system. -/
@[stacks 05PY]
theorem isEssentiallyConstantWith_of_bijective_homComparisonInv (M : I ⥤ C) [IsFiltered I]
    (X : C) (i : I) (r : X ⟶ M.obj i)
    (h : ∀ W : C, Function.Bijective (homComparisonInv M r W)) :
    ∃ (t : Cocone M), t.pt = X ∧
      ∃ (i' : I) (r' : t.pt ⟶ M.obj i'), IsEssentiallyConstantWith M t i' r' := by
  choose c hc using fun k => (h (M.obj k)).surjective
    (colimit.ι (homDiagram M (M.obj k)) k (𝟙 (M.obj k)))
  have refinement : ∀ k : I, ∃ (m : I) (σ : i ⟶ m) (τ : k ⟶ m),
      (c k ≫ r) ≫ M.map σ = 𝟙 (M.obj k) ≫ M.map τ := fun k =>
    (Types.FilteredColimit.colimit_eq_iff _).1 (hc k)
  have cocone_law : ∀ {k l : I} (φ : k ⟶ l), M.map φ ≫ c l = c k := by
    intro k l φ
    apply (h (M.obj k)).injective
    rw [hc k, homComparisonInv_apply, colimit_ι_eq_iff]
    obtain ⟨m, σ, τ, hmστ⟩ := refinement l
    refine ⟨m, σ, φ ≫ τ, ?_⟩
    simp only [Category.id_comp, Category.assoc, Functor.map_comp] at hmστ ⊢
    rw [hmστ]
  refine ⟨{ pt := X, ι := { app := c, naturality := ?_ } }, rfl, i, r, ?_, ?_⟩
  · intro k l φ
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    exact cocone_law φ
  · show r ≫ c i = 𝟙 X
    apply (h X).injective
    rw [homComparisonInv_apply, homComparisonInv_apply, colimit_ι_eq_iff]
    obtain ⟨m, σ, τ, hmστ⟩ := refinement i
    refine ⟨m, σ, τ, ?_⟩
    simp only [Category.id_comp, Category.assoc] at hmστ ⊢
    rw [hmστ]
  · intro j
    show ∃ (k : I) (σ : i ⟶ k) (τ : j ⟶ k), M.map τ = c j ≫ r ≫ M.map σ
    obtain ⟨k, σ, τ, hkστ⟩ := refinement j
    refine ⟨k, σ, τ, ?_⟩
    simp only [Category.id_comp, Category.assoc] at hkστ ⊢
    rw [← hkστ]

/-- For a filtered diagram `M : I ⥤ C` the four conditions (1) `M` is an essentially constant
ind-object, (2) some cocone has bijective `homComparison` at every `W`, (3) some colimit cocone
does, and (4) some `r : X ⟶ M i` has bijective `homComparisonInv` at every `W`, are equivalent. -/
@[stacks 05PY, sga "4 I 8.7.1.7" "partial"]
theorem essentiallyConstantInd_tfae (M : I ⥤ C) [IsFiltered I] :
    [ IsEssentiallyConstantInd M,
      HasCoconeWithBijectiveHomComparison M,
      HasColimitWithBijectiveHomComparison M,
      HasCoreflectionWithBijectiveHomComparison M ].TFAE := by
  tfae_have 1 → 3 := by
    rintro ⟨t, i, r, hr⟩
    exact ⟨t, hr.isColimit, fun W => hr.bijective_homComparison W⟩
  tfae_have 3 → 2 := by
    rintro ⟨t, _, hθ⟩
    exact ⟨t, hθ⟩
  tfae_have 2 → 1 := by
    rintro ⟨t, hθ⟩
    obtain ⟨i, r, hr⟩ := isEssentiallyConstantWith_of_bijective_homComparison M t hθ
    exact ⟨t, i, r, hr⟩
  tfae_have 1 → 4 := by
    rintro ⟨t, i, r, hr⟩
    exact ⟨t.pt, i, r, fun W => hr.bijective_homComparisonInv W⟩
  tfae_have 4 → 1 := by
    rintro ⟨X, i, r, hη⟩
    obtain ⟨t, _, i', r', hr'⟩ :=
      isEssentiallyConstantWith_of_bijective_homComparisonInv M X i r hη
    exact ⟨t, i', r', hr'⟩
  tfae_finish

end SmallIndex

end CategoryTheory.EssentiallyConstantInd
