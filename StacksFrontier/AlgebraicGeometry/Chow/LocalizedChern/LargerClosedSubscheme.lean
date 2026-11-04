module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseWhitney
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Localized
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationProduct
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantClassCopy

/-!
# Localized classes along a larger closed subscheme

Let `(S, δ)`, `X`, `E` and `p` be as in Situation 0GUJ, and let `Z ⊆ Z' ⊆ X` be closed
subschemes, with `E|_{X ∖ Z}` zero. **Stacks 0FB7** (Lemma 42.50.8) says that the localized
classes of Stacks 0FB2 for `Z'` are pushed forward from those for `Z`:

  `P_p(Z' ⟶ X, E) = (Z ⟶ Z')_* ∘ P_p(Z ⟶ X, E)`,
  resp.   `c_p(Z' ⟶ X, E) = (Z ⟶ Z')_* ∘ c_p(Z ⟶ X, E)`,

with `∘` as in Stacks 0EPK.

The source's proof: both classes are built from the same blowing up `b : W ⟶ 𝐏¹_X`, the same
perfect object `Q` on `W` and the same closed subscheme `T ⊆ W_∞`, and the comparison is Stacks
0FAI. This file carries it out for the localized class of a modification
(`Stacks.Chow.localizedModificationClass`) for every class `q ∈ A^p(W)` vanishing over `T`, and
then reads it at the classes of Stacks 0FB2.

## Main results

* `Stacks.Chow.localizedModificationClass_eq_bivariantProperPushforward` — the generic form of
  Stacks 0FB7: for `Z ⊆ Z'`, the localized class for `Z'` is `(Z ⟶ Z')_*` of the one for `Z`.
* `Stacks.Chow.graphPowerSumClass_eq_bivariantProperPushforward`,
  `Stacks.Chow.graphChernClass_eq_bivariantProperPushforward` — the same for the classes of the
  graph construction.
* `Stacks.Chow.LocalizedSituation.restriction_of_le` — condition (2) of Situation 0GUJ for
  `Z` gives it for `Z'`, so `Stacks.Chow.LocalizedSituation.withLargerClosed` is the
  situation for `Z'`.
* `Stacks.Chow.LocalizedSituation.localizedPowerSum_withLargerClosed`,
  `Stacks.Chow.LocalizedSituation.localizedChern_withLargerClosed` — **Stacks 0FB7**.

## Implementation notes

Write `π : W_∞ ⟶ X`, `E_Z = W_∞ ×_X Z` and `E_{Z'} = W_∞ ×_X Z'`, and `e : E_Z ⟶ E_{Z'}` for the
induced closed immersion. The class for `Z'` is `(E_{Z'} ⟶ Z')_* ∘ (q|_{E_{Z'}})' ∘ C`. The generic
form of Stacks 0FAI (`Stacks.Chow.bivariantProperPushforward_closedCoverExtension`) writes the
extension `(q|_{E_{Z'}})'` along `W_∞ = T ∪ E_{Z'}` as `e_*` of the extension of
`(q|_{E_{Z'}})|_{E_Z} = q|_{E_Z}` along `W_∞ = T ∪ E_Z`; then Stacks 0EPK moves `e_*` past the
composition with `C`, and the two pushforwards `E_Z ⟶ E_{Z'} ⟶ Z'` and `E_Z ⟶ Z ⟶ Z'` agree.
The classes involved live over different spellings of equal morphisms, so the comparison is made
up to heterogeneous equality.

## References

* [Stacks Project, Tag 0FB7](https://stacks.math.columbia.edu/tag/0FB7)
* [Stacks Project, Tag 0FAI](https://stacks.math.columbia.edu/tag/0FAI)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

namespace Stacks.Chow

/-! ### Congruences -/

section Congr

variable {C : ChowSituation.{u}}

/-- The extension along a closed cover is compatible with heterogeneous equality of the class
extended, over an equal second member of the cover. -/
theorem closedCoverExtension_heq_congr {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] {i₂ i₂' : X₂ ⟶ X}
    [IsClosedImmersion i₂] [IsClosedImmersion i₂'] (h : i₂ = i₂') {sX₂ sX₂' : X₂ ⟶ C.S}
    [LocallyOfFiniteType sX₂] [LocallyOfFiniteType sX₂'] (hs : sX₂ = sX₂')
    (hi₂ : i₂ ≫ sX = sX₂) (hi₂' : i₂' ≫ sX = sX₂') {p : ℤ}
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p}
    {a' : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂' p} (ha : a ≍ a')
    {hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ}
    {hcover' : Set.range i₁ ∪ Set.range i₂' = Set.univ}
    {hv : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)}
    {hv' : BivariantClass.VanishesOver a' (pullback.snd i₁ i₂')} :
    closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover hv ≍
      closedCoverExtension C sX i₁ i₂' sX₂' hi₂' a' hcover' hv' := by
  subst h hs
  cases ha
  rfl

/-- **Restriction of Stacks 0B7F is transitive.** Restricting a class `a ∈ A^p(Y)` along
`f : Y' ⟶ Y` and then along `e : Y'' ⟶ Y'` is restricting it along `e ≫ f`. -/
theorem chowCohomologyRestriction_chowCohomologyRestriction {Y Y' Y'' : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : Y' ⟶ Y) [LocallyOfFiniteType f]
    (e : Y'' ⟶ Y') [LocallyOfFiniteType e] {p : ℤ}
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) (f ≫ sY) e p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (chowCohomologyRestriction C (gysinSystemOfInvertible C) sY f p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a) ≍
      chowCohomologyRestriction C (gysinSystemOfInvertible C) sY (e ≫ f) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a := by
  refine heq_of_eq (BivariantClass.eq_of_idRule_eq C (e ≫ f ≫ sY) _ _ _
    fun {T} n _ k α ↦ ?_)
  rw [chowCohomologyRestriction_idRule, chowCohomologyRestriction_idRule]
  exact (chowCohomologyRestriction_idRule C sY (e ≫ f) a n k α).symm

/-- Restriction along equal morphisms gives heterogeneously equal classes. -/
theorem chowCohomologyRestriction_heq_congr {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {f f' : Y' ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (h : f = f') {p : ℤ} (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sY f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a ≍
      chowCohomologyRestriction C (gysinSystemOfInvertible C) sY f' p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a := by
  subst h
  rfl

/-- The pushforward of Stacks 0EPK is compatible with heterogeneous equality of the class, over
equal structure morphisms of the source, equal morphisms and equal degrees. -/
theorem bivariantProperPushforward_heq_congr_source {X Y Z : Scheme.{u}} {sX sX' : X ⟶ C.S}
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] (hs : sX = sX') {f f' : X ⟶ Y} [IsProper f]
    [IsProper f'] (hff' : f = f') {g g' : Y ⟶ Z} [LocallyOfFiniteType g] [LocallyOfFiniteType g']
    (hgg' : g = g') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX') (hg : g ≫ sZ = sY)
    (hg' : g' ≫ sZ = sY) {p p' : ℤ} (hp : p = p')
    {c : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) p}
    {c' : BivariantClass C (gysinSystemOfInvertible C) sX' sZ (f' ≫ g')
      (comp_comp_structureMorphism_eq hf' hg') p'} (hc : c ≍ c') :
    bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c ≍
      bivariantProperPushforwardOfInvertible C sX' sY sZ f' g' hf' hg' p' c' := by
  subst hs hff' hgg' hp
  cases hc
  rfl

/-- The composite of Stacks 0B75 is compatible with heterogeneous equality of the first factor,
over equal structure morphisms of the source, equal first morphisms and equal degrees. -/
theorem bivariantCompositeOfInvertible_heq_congr_source {X Y Z : Scheme.{u}} {sX sX' : X ⟶ C.S}
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] (hs : sX = sX') {f f' : X ⟶ Y}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (g : Y ⟶ Z) [LocallyOfFiniteType g]
    (hff' : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX') (hg : g ≫ sZ = sY) {p p' q : ℤ}
    (hp : p = p') {a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p}
    {a' : BivariantClass C (gysinSystemOfInvertible C) sX' sY f' hf' p'} (ha : a ≍ a')
    (d : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q) :
    bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a d ≍
      bivariantCompositeOfInvertible C sX' sY sZ f' g hf' hg p' q a' d := by
  subst hs hff' hp
  cases ha
  rfl

end Congr

/-! ### The localized class of a modification along a larger closed subscheme -/

section Modification

variable {C : ChowSituation.{u}} {X W Z Z' T : Scheme.{u}} {f : X ⟶ C.S} [LocallyOfFiniteType f]
  {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}
  (D : GysinAtInfinityData C (gysinSystemOfInvertible C) f b hA)
  {z : Z ⟶ X} [IsClosedImmersion z] {z' : Z' ⟶ X} [IsClosedImmersion z'] (j : Z ⟶ Z')
  [IsClosedImmersion j] (hj : j ≫ z' = z) (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {p : ℤ}
  {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}

include hj in
omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion z] [IsClosedImmersion z']
  [IsClosedImmersion j] [IsClosedImmersion t] in
/-- A closed subscheme `T ⊆ W_∞` containing every point of `W_∞` over `X ∖ Z` contains every
point over the smaller open `X ∖ Z'`. -/
theorem mem_range_of_notMem_range_of_comp
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t) :
    ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z' → w ∈ Set.range t := by
  refine fun w hw => hT w fun ⟨y, hy⟩ => hw ⟨j y, ?_⟩
  rw [← hy, ← hj, Scheme.Hom.comp_apply]

/-- The closed immersion `W_∞ ×_X Z ⟶ W_∞ ×_X Z'` induced by `j : Z ⟶ Z'`. -/
abbrev fibreAtInfinityPullbackMap :
    pullback (modificationProjectionAtInfinity f b) z ⟶
      pullback (modificationProjectionAtInfinity f b) z' :=
  pullback.lift (pullback.fst _ z) (pullback.snd _ z ≫ j)
    (by rw [pullback.condition, Category.assoc, hj])

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion z] [IsClosedImmersion z']
  [IsClosedImmersion j] in
/-- The map `W_∞ ×_X Z ⟶ W_∞ ×_X Z'` commutes with the projections to `W_∞`. -/
theorem fibreAtInfinityPullbackMap_fst :
    fibreAtInfinityPullbackMap j hj ≫ pullback.fst (modificationProjectionAtInfinity f b) z' =
      pullback.fst (modificationProjectionAtInfinity f b) z :=
  pullback.lift_fst _ _ _

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion z] [IsClosedImmersion z']
  [IsClosedImmersion j] in
/-- The map `W_∞ ×_X Z ⟶ W_∞ ×_X Z'` lies over `j : Z ⟶ Z'`. -/
theorem fibreAtInfinityPullbackMap_snd :
    fibreAtInfinityPullbackMap j hj ≫ pullback.snd (modificationProjectionAtInfinity f b) z' =
      pullback.snd (modificationProjectionAtInfinity f b) z ≫ j :=
  pullback.lift_snd _ _ _

/-- The map `W_∞ ×_X Z ⟶ W_∞ ×_X Z'` induced by `j` is a closed immersion. -/
instance isClosedImmersion_fibreAtInfinityPullbackMap :
    IsClosedImmersion (fibreAtInfinityPullbackMap (b := b) j hj) := by
  have : IsClosedImmersion (fibreAtInfinityPullbackMap j hj ≫
      pullback.fst (modificationProjectionAtInfinity f b) z') := by
    rw [fibreAtInfinityPullbackMap_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst (modificationProjectionAtInfinity f b) z')

/-- **The generic form of Stacks 0FB7.** Let `Z ⊆ Z' ⊆ X` be closed, with `j : Z ⟶ Z'`, let
`T ⊆ W_∞` be closed and contain every point of `W_∞` over `X ∖ Z`, and let `q ∈ A^p(W)` vanish over
`T`. Then the localized class of Stacks 0F9K for `Z'` is the pushforward along `j` (Stacks 0EPK)
of the one for `Z`: `q'_{Z'} = j_* ∘ q'_Z` in `A^p(Z' ⟶ X)`. -/
theorem localizedModificationClass_eq_bivariantProperPushforward
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b)) :
    localizedModificationClass D z' t (mem_range_of_notMem_range_of_comp j hj t hT) hq =
      bivariantProperPushforwardOfInvertible C (z ≫ f) (z' ≫ f) f j z'
        (by rw [← Category.assoc, hj]) rfl p
        ((localizedModificationClass D z t hT hq).congrHom hj.symm (by rw [hj])) := by
  set π := modificationProjectionAtInfinity f b with hπ
  set e := fibreAtInfinityPullbackMap (b := b) j hj with he
  have hT' := mem_range_of_notMem_range_of_comp j hj t hT
  set a := Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
    (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q with ha
  have hcov := range_union_range_pullbackFst_eq_univ z t hT
  have hcov' := range_union_range_pullbackFst_eq_univ z' t hT'
  have hcov'' : Set.range t ∪ Set.range (e ≫ pullback.fst π z') = Set.univ := by
    rw [fibreAtInfinityPullbackMap_fst]
    exact hcov
  have hv' : BivariantClass.VanishesOver
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) (π ≫ f)
        (pullback.fst π z') p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a)
      (pullback.snd t (pullback.fst π z')) :=
    BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
      (hq.chowCohomologyRestriction_modificationInclusionAtInfinity t)
  -- Stacks 0FAI: the extension for `Z'` is pushed forward from `W_∞ ×_X Z`
  have h0FAI := bivariantProperPushforward_closedCoverExtension C (π ≫ f) t t (pullback.fst π z')
    e (pullback.fst π z' ≫ π ≫ f) rfl hcov' hv' hcov'' hv'
  set Ext := closedCoverExtension C (π ≫ f) t (e ≫ pullback.fst π z')
    (e ≫ pullback.fst π z' ≫ π ≫ f) (by rw [Category.assoc])
    (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (pullback.fst π z' ≫ π ≫ f) e p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) (π ≫ f)
        (pullback.fst π z') p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a))
    hcov'' (hv'.chowCohomologyRestriction_pullbackSnd C t (pullback.fst π z') e) with hExt
  have hext : modificationExtension z' t hT' hq =
      bivariantProperPushforwardOfInvertible C (e ≫ pullback.fst π z' ≫ π ≫ f)
        (pullback.fst π z' ≫ π ≫ f)
        (π ≫ f) e (pullback.fst π z') rfl rfl p Ext := h0FAI.symm
  -- `Ext` is the extension used for `Z`
  have hsrc : e ≫ pullback.fst π z' ≫ π ≫ f = pullback.fst π z ≫ π ≫ f := by
    rw [← Category.assoc, fibreAtInfinityPullbackMap_fst]
  have hExtZ : Ext ≍ modificationExtension z t hT hq := by
    unfold modificationExtension
    refine closedCoverExtension_heq_congr (π ≫ f) t (fibreAtInfinityPullbackMap_fst j hj) hsrc
      _ rfl ?_ (hv' := BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
        (hq.chowCohomologyRestriction_modificationInclusionAtInfinity t))
    exact (chowCohomologyRestriction_chowCohomologyRestriction (π ≫ f) (pullback.fst π z') e
      a).trans (chowCohomologyRestriction_heq_congr (π ≫ f)
        (fibreAtInfinityPullbackMap_fst j hj) a)
  -- Stacks 0EPK: pushing forward along `e` commutes with composing with the class at infinity
  have hcomp := bivariantProperPushforwardOfInvertible_bivariantCompositeOfInvertible C
    (e ≫ pullback.fst π z' ≫ π ≫ f) (pullback.fst π z' ≫ π ≫ f) (π ≫ f) f e (pullback.fst π z') π
    rfl rfl rfl p 0 Ext D.bivariantClass
  have hcond : (e ≫ pullback.fst π z') ≫ π = (e ≫ pullback.snd π z') ≫ z' := by
    rw [Category.assoc, pullback.condition, Category.assoc]
  have hcondR : pullback.fst π z ≫ π = (pullback.snd π z ≫ j) ≫ z' := by
    rw [Category.assoc, hj, pullback.condition]
  -- the left-hand side as one pushforward along `W_∞ ×_X Z ⟶ W_∞ ×_X Z' ⟶ Z'`
  have hL : localizedModificationClass D z' t hT' hq =
      bivariantProperPushforwardOfInvertible C (e ≫ pullback.fst π z' ≫ π ≫ f) (z' ≫ f) f
        (e ≫ pullback.snd π z') z'
        (by rw [Category.assoc, pullbackSnd_comp_structureMorphism rfl z'])
        rfl p
        (BivariantClass.copy C _ _ f hcond _ _ (add_zero p)
          (bivariantCompositeOfInvertible C _ _ f (e ≫ pullback.fst π z') π
            (by rw [Category.assoc]) rfl p 0 Ext D.bivariantClass)) := by
    rw [bivariantProperPushforwardOfInvertible_comp C (e ≫ pullback.fst π z' ≫ π ≫ f)
      (pullback.fst π z' ≫ π ≫ f) (z' ≫ f) f e (pullback.snd π z') z' rfl
      (pullbackSnd_comp_structureMorphism rfl z') rfl p]
    unfold localizedModificationClass
    rw [hext]
    refine congrArg _ (eq_of_heq ?_)
    refine (BivariantClass.copy_heq _ _ _ _ _).trans ?_
    rw [← hcomp]
    refine bivariantProperPushforward_heq_congr_source rfl rfl pullback.condition _ _ _ _
      (add_zero p) ?_
    refine (BivariantClass.congrHom_heq _ _ _).trans ?_
    refine HEq.trans ?_ (BivariantClass.congrHom_heq _ _ _).symm
    exact (BivariantClass.copy_heq _ _ _ _ _).symm
  -- the right-hand side as one pushforward along `W_∞ ×_X Z ⟶ Z ⟶ Z'`
  have hR : bivariantProperPushforwardOfInvertible C (z ≫ f) (z' ≫ f) f j z'
        (by rw [← Category.assoc, hj]) rfl p
        ((localizedModificationClass D z t hT hq).congrHom hj.symm (by rw [hj])) =
      bivariantProperPushforwardOfInvertible C (pullback.fst π z ≫ π ≫ f) (z' ≫ f) f
        (pullback.snd π z ≫ j) z'
        (by rw [Category.assoc, ← Category.assoc j, hj, pullbackSnd_comp_structureMorphism rfl z])
        rfl p
        (BivariantClass.copy C _ _ f hcondR _ _ (add_zero p)
          (bivariantCompositeOfInvertible C _ _ f (pullback.fst π z) π rfl rfl p 0
            (modificationExtension z t hT hq) D.bivariantClass)) := by
    rw [bivariantProperPushforwardOfInvertible_comp C (pullback.fst π z ≫ π ≫ f) (z ≫ f) (z' ≫ f) f
      (pullback.snd π z) j z' (pullbackSnd_comp_structureMorphism rfl z)
      (by rw [← Category.assoc, hj]) rfl p]
    refine congrArg _ (eq_of_heq ?_)
    refine (BivariantClass.congrHom_heq _ _ _).trans ?_
    unfold localizedModificationClass
    refine bivariantProperPushforward_heq_congr_source rfl rfl hj.symm _ _ _ _ rfl ?_
    refine (BivariantClass.copy_heq _ _ _ _ _).trans ?_
    refine HEq.trans ?_ (BivariantClass.congrHom_heq _ _ _).symm
    exact (BivariantClass.copy_heq _ _ _ _ _).symm
  rw [hL, hR]
  refine eq_of_heq (bivariantProperPushforward_heq_congr_source hsrc
    (fibreAtInfinityPullbackMap_snd j hj) rfl _ _ _ _ rfl ?_)
  refine (BivariantClass.copy_heq _ _ _ _ _).trans (HEq.trans ?_
    (BivariantClass.copy_heq _ _ _ _ _).symm)
  exact bivariantCompositeOfInvertible_heq_congr_source hsrc π
    (fibreAtInfinityPullbackMap_fst j hj) _ _ rfl rfl hExtZ D.bivariantClass
end Modification

/-! ### The classes of the graph construction, and Stacks 0FB7 -/

attribute [local instance 10000] HasDerivedCategory.standard

section Graph

variable (C : ChowSituation.{u}) {X Z Z' T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
  {z : Z ⟶ X} [IsClosedImmersion z] {z' : Z' ⟶ X} [IsClosedImmersion z'] (j : Z ⟶ Z')
  [IsClosedImmersion j] (hj : j ≫ z' = z)
  (t : T ⟶ modificationFibreAtInfinity f (graphBlowupToBase f E hE)) [IsClosedImmersion t]
  (hH : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (graphObjectRestrictHomology f E hE t n))
  (hQ : HasDefinedChernClasses (graphObject f E hE)) (p : ℕ)
  (hT : ∀ w, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) w ∉ Set.range z →
    w ∈ Set.range t)

include hj in
omit [LocallyOfFiniteType f] [IsClosedImmersion z] [IsClosedImmersion z']
  [IsClosedImmersion j] [IsClosedImmersion t] in
/-- A condition on the points of `T` lying over `X ∖ Z` holds in particular at the points lying
over the smaller open `X ∖ Z'`. -/
theorem forall_notMem_range_of_comp {P : T → Prop}
    (h : ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉
      Set.range z → P τ) :
    ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉
      Set.range z' → P τ := by
  refine fun τ hτ => h τ fun ⟨y, hy⟩ => hτ ⟨j y, ?_⟩
  rw [← hy, ← hj, Scheme.Hom.comp_apply]

/-- **Stacks 0FB7 for the class `P_p(Z ⟶ X, E)` of the graph construction.** For closed
`Z ⊆ Z' ⊆ X`, the class for `Z'` is the pushforward along `j : Z ⟶ Z'` of the class for `Z`. -/
theorem graphPowerSumClass_eq_bivariantProperPushforward
    (hrk : ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉
      Set.range z → ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) :
    graphPowerSumClass C f E hE z' t hH hQ p (mem_range_of_notMem_range_of_comp j hj t hT)
        (forall_notMem_range_of_comp C f E hE j hj t hrk) =
      bivariantProperPushforwardOfInvertible C (z ≫ f) (z' ≫ f) f j z'
        (by rw [← Category.assoc, hj]) rfl p
        ((graphPowerSumClass C f E hE z t hH hQ p hT hrk).congrHom hj.symm (by rw [hj])) :=
  localizedModificationClass_eq_bivariantProperPushforward _ j hj _
    (mem_range_graphZeroLocus C f E hE z t hH hT hrk)
    (vanishesOver_perfectPowerSumClass_of_isZero C _ _ hQ p
      (isZero_derivedPullback_graphZeroLocus f E hE t hH))

/-- **Stacks 0FB7 for the class `c_p(Z ⟶ X, E)` of the graph construction.** For closed
`Z ⊆ Z' ⊆ X`, the class for `Z'` is the pushforward along `j : Z ⟶ Z'` of the class for `Z`. -/
theorem graphChernClass_eq_bivariantProperPushforward
    (hrk : ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉
      Set.range z →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T _ (hH 0) τ < p) :
    graphChernClass C f E hE z' t hH hQ p (mem_range_of_notMem_range_of_comp j hj t hT)
        (forall_notMem_range_of_comp C f E hE j hj t hrk) =
      bivariantProperPushforwardOfInvertible C (z ≫ f) (z' ≫ f) f j z'
        (by rw [← Category.assoc, hj]) rfl p
        ((graphChernClass C f E hE z t hH hQ p hT hrk).congrHom hj.symm (by rw [hj])) :=
  localizedModificationClass_eq_bivariantProperPushforward _ j hj _
    (mem_range_graphSmallRankLocus C f E hE z t hH p hT hrk)
    (vanishesOver_perfectChernClass_of_rankLT C _ _ hQ p
      (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_graphSmallRankLocus f E hE t hH p))

end Graph

/-! ### Restricting condition (2) of Situation 0GUJ to a smaller open -/

section Restriction

variable {V X Z : Scheme.{u}} {i : Z ⟶ X} {a : V ⟶ Z} {k : V ⟶ X} (h : a ≫ i = k)
  {E : DerivedCategory X.Modules}

/-- The derived pullback of `E` along `k = a ≫ i` is the derived pullback along `a` of the derived
pullback along `i`. -/
private def derivedPullbackIsoOfFactors (h : a ≫ i = k) :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback k.toLRSHom.toShHom).obj E ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback a.toLRSHom.toShHom).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback i.toLRSHom.toShHom).obj E) :=
  have hsq : k.toLRSHom.toShHom = a.toLRSHom.toShHom ≫ i.toLRSHom.toShHom :=
    congrArg (fun f => f.toLRSHom.toShHom) h.symm
  (eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq hsq)).app E ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      a.toLRSHom.toShHom i.toLRSHom.toShHom).app E).symm

include h in
/-- If `E|_Z` is zero, the derived pullback of `E` along a morphism factoring through
`i : Z ⟶ X` is zero. -/
theorem isZero_derivedPullback_of_factors
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i.toLRSHom.toShHom).obj E)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      k.toLRSHom.toShHom).obj E) :=
  IsZero.of_iso (Functor.map_isZero
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback a.toLRSHom.toShHom) hzero)
    (derivedPullbackIsoOfFactors h)

include h in
/-- If `E|_Z` is a finite locally free module of rank `< p` placed in degree `0`, so is the
derived pullback of `E` along a morphism factoring through `i : Z ⟶ X`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_factors {p : ℕ}
    (hrank : ∃ M : Z.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        i.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ M : V.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        k.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hrank
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := hM.1
  exact ⟨(Scheme.Modules.pullback a).obj M, hM.pullback a,
    ⟨derivedPullbackIsoOfFactors h ≪≫
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback a.toLRSHom.toShHom).mapIso e ≪≫
      derivedPullbackSingleIsoOfIsFiniteLocallyFree a M⟩⟩

end Restriction

namespace LocalizedSituation

variable (S : LocalizedSituation.{u}) {Z' : Scheme.{u}} (i' : Z' ⟶ S.X)
  [IsClosedImmersion i'] (j : S.Z ⟶ Z') [IsClosedImmersion j] (hj : j ≫ i' = S.i)

include hj in
omit [IsClosedImmersion j] in
/-- `X ∖ Z' ⊆ X ∖ Z` for `Z ⊆ Z'`. -/
theorem compl_range_le :
    (⟨(Set.range i'.base)ᶜ, i'.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : S.X.Opens) ≤
      ⟨(Set.range S.i.base)ᶜ, S.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ := by
  intro x hx ⟨y, hy⟩
  exact hx ⟨j y, by rw [← hy, ← hj, Scheme.Hom.comp_apply]⟩

omit [IsClosedImmersion j] in
include hj in
/-- If `E|_{X ∖ Z}` is zero, so is `E|_{X ∖ Z'}`. -/
theorem isZero_of_isZeroOnComplement (h : S.IsZeroOnComplement) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (S.X.toRingedSpace.ofRestrict (⟨(Set.range i'.base)ᶜ,
        i'.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : S.X.Opens).isOpenEmbedding)).obj
      S.E) :=
  isZero_derivedPullback_of_factors (i := Scheme.Opens.ι _) (k := Scheme.Opens.ι _)
    (S.X.homOfLE_ι (S.compl_range_le i' j hj)) h

omit [IsClosedImmersion j] in
include hj in
/-- If `E|_{X ∖ Z}` is finite locally free of rank `< p` in degree `0`, so is `E|_{X ∖ Z'}`. -/
theorem exists_of_isFiniteLocallyFreeOfRankLTOnComplement
    (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    ∃ M : OXMod.{u, u, u} (S.X.toRingedSpace.restrict (⟨(Set.range i'.base)ᶜ,
        i'.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : S.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M S.p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (S.X.toRingedSpace.ofRestrict (⟨(Set.range i'.base)ᶜ,
            i'.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : S.X.Opens).isOpenEmbedding)).obj
          S.E ≅ (DerivedCategory.singleFunctor _ 0).obj M) :=
  exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_factors (i := Scheme.Opens.ι _)
    (k := Scheme.Opens.ι _) (S.X.homOfLE_ι (S.compl_range_le i' j hj)) h

omit [IsClosedImmersion j] in
include hj in
/-- **Condition (2) of Situation 0GUJ passes to a larger closed subscheme**: if `E|_{X ∖ Z}` is
zero, resp. finite locally free of rank `< p` in degree `0`, then so is `E|_{X ∖ Z'}`. -/
theorem restriction_of_le :
    letI U : TopologicalSpace.Opens S.X :=
      ⟨(Set.range i'.base)ᶜ, i'.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    letI F := Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (S.X.toRingedSpace.ofRestrict U.isOpenEmbedding)
    IsZero (F.obj S.E) ∨
      ∃ M : OXMod.{u, u, u} (S.X.toRingedSpace.restrict U.isOpenEmbedding),
        IsFiniteLocallyFreeOfRankLT M S.p ∧
          Nonempty (F.obj S.E ≅ (DerivedCategory.singleFunctor _ 0).obj M) :=
  S.isZeroOnComplement_or.imp (S.isZero_of_isZeroOnComplement i' j hj)
    (S.exists_of_isFiniteLocallyFreeOfRankLTOnComplement i' j hj)

/-- The situation of Stacks 0GUJ with the closed subscheme `Z` replaced by a larger closed
subscheme `Z'` of `X`, everything else unchanged. -/
def withLargerClosed : LocalizedSituation.{u} where
  base := S.base
  X := S.X
  a := S.a
  locallyOfFiniteType := S.locallyOfFiniteType
  Z := Z'
  i := i'
  E := S.E
  p := S.p
  perfect := S.perfect
  restriction := restriction_of_le S i' j hj
  finiteness := S.finiteness

variable {S} {i' j hj}

omit [IsClosedImmersion j] in
/-- If `E|_{X ∖ Z}` is zero, so is `E|_{X ∖ Z'}`. -/
theorem IsZeroOnComplement.withLargerClosed (h : S.IsZeroOnComplement) :
    (S.withLargerClosed i' j hj).IsZeroOnComplement :=
  S.isZero_of_isZeroOnComplement i' j hj h

omit [IsClosedImmersion j] in
/-- If `E|_{X ∖ Z}` is finite locally free of rank `< p` in degree `0`, so is `E|_{X ∖ Z'}`. -/
theorem IsFiniteLocallyFreeOfRankLTOnComplement.withLargerClosed
    (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    (S.withLargerClosed i' j hj).IsFiniteLocallyFreeOfRankLTOnComplement :=
  S.exists_of_isFiniteLocallyFreeOfRankLTOnComplement i' j hj h

/-- **Stacks 0FB7** (Lemma 42.50.8), for `P_p`. In Situation 0GUJ with `E|_{X ∖ Z}` zero, let
`Z ⊆ Z' ⊆ X` be closed, with `j : Z ⟶ Z'`. Then
`P_p(Z' ⟶ X, E) = (Z ⟶ Z')_* ∘ P_p(Z ⟶ X, E)` in `A^p(Z' ⟶ X)`, with `∘` as in Stacks 0EPK; the
class `P_p(Z' ⟶ X, E)` is that of the situation
`Stacks.Chow.LocalizedSituation.withLargerClosed` for `Z'`. -/
@[stacks 0FB7 "for P_p"]
theorem localizedPowerSum_withLargerClosed (h : S.IsZeroOnComplement) (p : ℕ) :
    (S.withLargerClosed i' j hj).localizedPowerSum h.withLargerClosed p =
      bivariantProperPushforwardOfInvertible S.base (S.i ≫ S.a) (i' ≫ S.a) S.a j i'
        (by rw [← Category.assoc, hj]) rfl p
        ((S.localizedPowerSum h p).congrHom hj.symm (by rw [hj])) :=
  graphPowerSumClass_eq_bivariantProperPushforward S.base S.a S.E S.perfect j hj
    S.graphSubschemeι S.isFiniteLocallyFree_graphObjectRestrictHomology
    S.hasDefinedChernClasses_graphObject p
    S.mem_range_graphSubschemeι (S.finiteLocallyFreeRank_graphSubscheme_eq_zero h)

/-- **Stacks 0FB7** (Lemma 42.50.8), for `c_p`. In Situation 0GUJ with `E|_{X ∖ Z}` finite
locally free of rank `< p` in degree `0`, let `Z ⊆ Z' ⊆ X` be closed, with `j : Z ⟶ Z'`. Then
`c_p(Z' ⟶ X, E) = (Z ⟶ Z')_* ∘ c_p(Z ⟶ X, E)` in `A^p(Z' ⟶ X)`, with `∘` as in Stacks 0EPK; the
class `c_p(Z' ⟶ X, E)` is that of the situation
`Stacks.Chow.LocalizedSituation.withLargerClosed` for `Z'`. -/
@[stacks 0FB7 "for c_p"]
theorem localizedChern_withLargerClosed (h : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    (S.withLargerClosed i' j hj).localizedChern h.withLargerClosed =
      bivariantProperPushforwardOfInvertible S.base (S.i ≫ S.a) (i' ≫ S.a) S.a j i'
        (by rw [← Category.assoc, hj]) rfl S.p
        ((S.localizedChern h).congrHom hj.symm (by rw [hj])) :=
  graphChernClass_eq_bivariantProperPushforward S.base S.a S.E S.perfect j hj
    S.graphSubschemeι S.isFiniteLocallyFree_graphObjectRestrictHomology
    S.hasDefinedChernClasses_graphObject S.p
    S.mem_range_graphSubschemeι (S.finiteLocallyFreeRank_graphSubscheme_lt h)

end LocalizedSituation

end Stacks.Chow

end
