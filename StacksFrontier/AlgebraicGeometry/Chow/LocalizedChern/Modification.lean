module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityLift
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Pushforward
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ChowCohomologyRestriction

/-!
# The localized class of a modification of the projective line

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `Z ⊆ X` be a closed subscheme, and let `b : W ⟶ 𝐏¹_X` be a proper
morphism which is an isomorphism over `𝐀¹_X`, with fibre at infinity `i_∞ : W_∞ ⟶ W` and section
at zero `i_0 : X ⟶ W`. Let `C ∈ A⁰(W_∞ ⟶ X)` be a class with `i_{∞,*} ∘ C = i_{0,*}`, as provided
by Stacks 0F9J. Let `T ⊆ W_∞` be a closed subscheme containing every point of `W_∞` lying over
`X ∖ Z`, so that `W_∞ = T ∪ E` set-theoretically for `E = W_∞ ×_X Z`.

Stacks 0F9K attaches to a perfect object `Q` on `W` with `Q|_T` zero (resp. finite locally free of
rank `< p`) the class

  `P'_p(Q) = (E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C ∈ A^p(Z ⟶ X)`,

and proves `(Z ⟶ X)_* ∘ P'_p(Q) = P_p(Q|_{X × {0}})`. Only two properties of `P_p(Q)` enter: it is
a class `q ∈ A^p(W)`, and its restriction to `T` vanishes. This file makes the construction and
proves the identity for every such class `q`:

  `q' = (E ⟶ Z)_* ∘ (q|_E)' ∘ C`   and   `(Z ⟶ X)_* ∘ q' = i_0^* q`,

where `(q|_E)' ∈ A^p(E ⟶ W_∞)` is the extension of `q|_E` along the closed cover `W_∞ = T ∪ E`
(the construction of Stacks 0F9H).

## Main definitions

* `Stacks.Chow.modificationExtension` — the class `(q|_E)' ∈ A^p(E ⟶ W_∞)`.
* `Stacks.Chow.localizedModificationClass` — the class `q' ∈ A^p(Z ⟶ X)`.

## Main results

* `Stacks.Chow.properPushforwardChowCohomology_localizedModificationClass` — the generic form of
  Stacks 0F9K: `(Z ⟶ X)_* ∘ q' = i_0^* q` in `A^p(X)`.
* `Stacks.Chow.localizedModificationClass_add` — `q'` is additive in `q`.
* `Stacks.Chow.localizedModificationClass_eq` — `q'` does not depend on `T`, the generic form of
  the first assertion of Stacks 0FAU.
* `Stacks.Chow.chowPush_idRule_bivariantClass_cap_heq` — for every class `q ∈ A^p(W)`, pushing
  `q|_{W_∞} ∩ (C ∩ α)` forward to the test scheme gives `i_0^* q ∩ α`.

## Implementation notes

The class `C` and its identity `i_{∞,*} ∘ C = i_{0,*}` are taken from a structure
`Stacks.Chow.GysinAtInfinityData`, the record of the conclusion of Stacks 0F9J; every result here
holds for every inhabitant of it, and the statement of Stacks 0F9K is the instance at the class of
Stacks 0F9J and at `q = P_p(Q)`, resp. `c_p(Q)`, whose restriction to `T` vanishes by the
hypothesis on `Q|_T`.

The hypothesis on `T` is stated pointwise, as in the source;
`Stacks.Chow.range_union_range_pullbackFst_eq_univ` turns it into the closed cover
`W_∞ = T ∪ E`. The vanishing of `q` over `T` is `Stacks.Chow.BivariantClass.VanishesOver`, which
by `Stacks.Chow.chowCohomologyRestriction_eq_zero_iff_vanishesOver` is the vanishing of the
restriction of `q` to `T`.

The composite `(q|_E)' ∘ C` is a class of degree `p + 0` for `E ⟶ W_∞ ⟶ X`; it is read as a class
of degree `p` for `E ⟶ Z ⟶ X` by `Stacks.Chow.BivariantClass.copy` before it is pushed forward,
and `i_0^* q`, a class against the structure morphism `X ⟶ W ⟶ S`, is read against that of `X`
by `Stacks.Chow.bivariantClassCongrBase`.

## References

* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9I](https://stacks.math.columbia.edu/tag/0F9I)
* [Stacks Project, Tag 0FAU](https://stacks.math.columbia.edu/tag/0FAU)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Pushing cap products forward to the test scheme -/

section PushToTestScheme

variable {C : ChowSituation.{u}} {A B Y : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA]
  {sB : B ⟶ C.S} [LocallyOfFiniteType sB] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- Pushed forward to the test scheme, the cap product of a class read for an equal morphism and
an equal degree (`Stacks.Chow.BivariantClass.copy`) is that of the class. -/
theorem chowPush_pullbackSnd_copy_cap_heq {G : GysinSystem C} {F F' : A ⟶ Y} [IsProper F]
    [IsProper F'] (hFF' : F = F') (hF : F ≫ sY = sA) (hF' : F' ≫ sY = sA) {p p' : ℤ}
    (hpp' : p = p') (c : BivariantClass C G sA sY F hF p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    chowPush C (pullback.fst F' g ≫ sA) (g ≫ sY) (pullback.snd F' g)
        (pullbackSnd_comp_structureMorphism hF' g) (k - p')
        ((BivariantClass.copy C G sA sY hFF' hF hF' hpp' c).cap g k α) ≍
      chowPush C (pullback.fst F g ≫ sA) (g ≫ sY) (pullback.snd F g)
        (pullbackSnd_comp_structureMorphism hF g) (k - p) (c.cap g k α) := by
  subst hFF'
  subst hpp'
  rfl

/-- Pushed forward to the test scheme, the cap product of the composite `a ∘ b` of Stacks 0B75 is
the cap product of `a` on the cap product of `b`, pushed forward in two steps. The two sides lie in
the degrees `k - (p + q)` and `(k - q) - p`. -/
theorem chowPush_pullbackSnd_bivariantCompositeOfInvertible_cap_heq (F₁ : A ⟶ B) [IsProper F₁]
    (F₂ : B ⟶ Y) [IsProper F₂] (hF₁ : F₁ ≫ sB = sA) (hF₂ : F₂ ≫ sY = sB) (p q : ℤ)
    (a : BivariantClass C (gysinSystemOfInvertible C) sA sB F₁ hF₁ p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sB sY F₂ hF₂ q) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    chowPush C (pullback.fst (F₁ ≫ F₂) g ≫ sA) (g ≫ sY) (pullback.snd (F₁ ≫ F₂) g)
        (pullbackSnd_comp_structureMorphism (comp_comp_structureMorphism_eq hF₁ hF₂) g)
        (k - (p + q))
        ((bivariantCompositeOfInvertible C sA sB sY F₁ F₂ hF₁ hF₂ p q a b).cap g k α) ≍
      chowPush C (pullback.fst F₂ g ≫ sB) (g ≫ sY) (pullback.snd F₂ g)
        (pullbackSnd_comp_structureMorphism hF₂ g) ((k - q) - p)
        (chowPush C (pullback.fst F₁ (pullback.fst F₂ g) ≫ sA) (pullback.fst F₂ g ≫ sB)
          (pullback.snd F₁ (pullback.fst F₂ g)) (pullbackSnd_comp_structureMorphism hF₁ _)
          ((k - q) - p) (a.cap (pullback.fst F₂ g) (k - q) (b.cap g k α))) := by
  have h₁ := isBivariantClassComposition_bivariantCompositeOfInvertible C sA sB sY F₁ F₂ hF₁ hF₂
    p q a b g k α
  refine (heq_map_index (by ring : k - (p + q) = (k - q) - p) h₁ fun n x ↦
    chowPush C (pullback.fst (F₁ ≫ F₂) g ≫ sA) (g ≫ sY) (pullback.snd (F₁ ≫ F₂) g)
      (pullbackSnd_comp_structureMorphism (comp_comp_structureMorphism_eq hF₁ hF₂) g) n
      x).trans (heq_of_eq ?_)
  rw [bivariantCompositeCap_apply, chowPush_comp C _ _ _ (pullback.snd F₁ (pullback.fst F₂ g))
    (pullback.snd F₂ g) _ rfl _ _
    (by rw [Category.assoc, pullbackSnd_comp_structureMorphism hF₂ g,
      pullbackSnd_comp_structureMorphism hF₁])]
  exact (properChowPushforward_comp_apply C _ _ _ (pullbackRightPullbackFstIso F₂ g F₁).hom
    (pullback.snd (F₁ ≫ F₂) g) _ (pullbackRightPullbackFstIso_hom_snd F₂ g F₁) _ _ _ _ _ _ _
    _).symm

/-- The operation of a Chow cohomology class read against an equal structure morphism
(`Stacks.Chow.bivariantClassCongrBase`) is that of the class, through the transports between the
Chow groups of the two structure morphisms. -/
theorem BivariantClass.idRule_bivariantClassCongrBase {G : GysinSystem C} {sY' : Y ⟶ C.S}
    [LocallyOfFiniteType sY'] (h : sY = sY') {p : ℤ} (c : chowCohomologyComponent C G sY p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY') k) :
    (bivariantClassCongrBase C G (𝟙 Y) h h (hv := Category.id_comp sY)
        (hv' := Category.id_comp sY') p c).idRule C sY' G g k α =
      chowGroupCongr C (by rw [h]) (k - p)
        (c.idRule C sY G g k (chowGroupCongr C (by rw [h]) k α)) := by
  subst h
  rfl

end PushToTestScheme

/-! ### The localized class -/

section Modification

variable {C : ChowSituation.{u}} {X W Z T : Scheme.{u}} {f : X ⟶ C.S} [LocallyOfFiniteType f]
  {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}
  (D : GysinAtInfinityData C (gysinSystemOfInvertible C) f b hA)
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {p : ℤ}
  {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion z] [IsClosedImmersion t] in
/-- If a closed subscheme `T ⊆ W_∞` contains every point of `W_∞` lying over `X ∖ Z`, then
`W_∞ = T ∪ E` set-theoretically, for `E = W_∞ ×_X Z`. -/
theorem range_union_range_pullbackFst_eq_univ
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t) :
    Set.range t ∪ Set.range (pullback.fst (modificationProjectionAtInfinity f b) z) =
      Set.univ := by
  refine Set.eq_univ_of_forall fun w ↦ ?_
  rw [Scheme.Pullback.range_fst]
  by_cases hw : modificationProjectionAtInfinity f b w ∈ Set.range z
  · exact Or.inr hw
  · exact Or.inl (hT w hw)

/-- If `q ∈ A^p(W)` vanishes over `T ⊆ W_∞`, its restriction `q|_{W_∞}` vanishes over `T`. -/
theorem BivariantClass.VanishesOver.chowCohomologyRestriction_modificationInclusionAtInfinity
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b)) :
    BivariantClass.VanishesOver
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q) t :=
  hq.chowCohomologyRestriction_of_comp (modificationInclusionAtInfinity f b) t (𝟙 T)
    (Category.id_comp _)

/-- **The class `P'_p(Q|_E)` of the proof of Stacks 0F9K, for a general class.** Let `T ⊆ W_∞` be
closed and contain every point of `W_∞` over `X ∖ Z`, so that `W_∞ = T ∪ E` with
`E = W_∞ ×_X Z`, and let `q ∈ A^p(W)` vanish over `T`. This is the extension
`(q|_E)' ∈ A^p(E ⟶ W_∞)` of `q|_E` along the closed cover `W_∞ = T ∪ E`
(`Stacks.Chow.closedCoverExtension`), `q|_E` being the restriction of `q|_{W_∞}`. -/
def modificationExtension
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b)) :
    BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl p :=
  closedCoverExtension C (modificationProjectionAtInfinity f b ≫ f) t
    (pullback.fst (modificationProjectionAtInfinity f b) z) _ rfl
    (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q))
    (range_union_range_pullbackFst_eq_univ z t hT)
    (BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
      (hq.chowCohomologyRestriction_modificationInclusionAtInfinity t))

/-- **The localized class of Stacks 0F9K, for a general class.** For `q ∈ A^p(W)` vanishing over
a closed `T ⊆ W_∞` containing every point of `W_∞` over `X ∖ Z`, the class
`q' = (E ⟶ Z)_* ∘ (q|_E)' ∘ C ∈ A^p(Z ⟶ X)`, where `E = W_∞ ×_X Z`, `(q|_E)'` is
`Stacks.Chow.modificationExtension`, `C ∈ A⁰(W_∞ ⟶ X)` is the class recorded by `D`, `∘` is the
composition of Stacks 0B75 and `(E ⟶ Z)_*` the pushforward of Stacks 0EPK. The composite, a class
of degree `p + 0` for `E ⟶ W_∞ ⟶ X`, is read as a class of degree `p` for `E ⟶ Z ⟶ X`. -/
def localizedModificationClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b)) :
    BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p :=
  bivariantProperPushforwardOfInvertible C _ (z ≫ f) f
    (pullback.snd (modificationProjectionAtInfinity f b) z)
    z (pullbackSnd_comp_structureMorphism rfl z) rfl p
    (BivariantClass.copy C _ _ f pullback.condition _ _ (add_zero p)
      (bivariantCompositeOfInvertible C _ _ f
        (pullback.fst (modificationProjectionAtInfinity f b) z)
        (modificationProjectionAtInfinity f b) rfl rfl p 0 (modificationExtension z t hT hq)
        D.bivariantClass))

/-- Pushed forward to the test scheme, the cap product of the localized class is that of the
restriction `q|_{W_∞}` on the cap product of the class at infinity. -/
theorem chowPush_localizedModificationClass_cap_heq
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    {V : Scheme.{u}} (g : V ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ f) k) :
    chowPush C (pullback.fst z g ≫ (z ≫ f)) (g ≫ f) (pullback.snd z g)
        (pullbackSnd_comp_structureMorphism rfl g) (k - p)
        ((localizedModificationClass D z t hT hq).cap g k α) ≍
      chowPush C (pullback.fst (modificationProjectionAtInfinity f b) g ≫
          (modificationProjectionAtInfinity f b ≫ f)) (g ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) g)
        (pullbackSnd_comp_structureMorphism rfl g) ((k - 0) - p)
        ((Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
          (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q).idRule C
          (modificationProjectionAtInfinity f b ≫ f) (gysinSystemOfInvertible C)
          (pullback.fst (modificationProjectionAtInfinity f b) g) (k - 0)
          (D.bivariantClass.cap g k α)) := by
  unfold localizedModificationClass
  rw [chowPush_pullbackSnd_bivariantProperPushforward_cap]
  refine (chowPush_pullbackSnd_copy_cap_heq _ _ _ _ _ g k α).trans
    ((chowPush_pullbackSnd_bivariantCompositeOfInvertible_cap_heq _ _ _ _ _ _ _ _ g k
      α).trans (heq_of_eq ?_))
  refine congrArg _ ?_
  unfold modificationExtension
  exact chowPush_closedCoverExtension_cap C _ t _ (range_union_range_pullbackFst_eq_univ z t hT)
    (hq.chowCohomologyRestriction_modificationInclusionAtInfinity t) _ (k - 0) _

/-- The section at zero `i_0 : X ⟶ W` is a closed immersion. -/
instance isClosedImmersion_modificationSectionAtZero
    (h : IsIso (modificationFibreAtZeroProjection f b)) :
    IsClosedImmersion (modificationSectionAtZero f b h) := by
  unfold modificationSectionAtZero
  infer_instance

/-- For every `q ∈ A^p(W)` and every test scheme `g : V ⟶ X`, pushing `q|_{W_∞} ∩ (C ∩ α)`
forward along `W_∞ ×_X V ⟶ V` gives `i_0^* q ∩ α`. The two sides lie in the degrees
`(k - 0) - p` and `k - p`. -/
theorem chowPush_idRule_bivariantClass_cap_heq {V : Scheme.{u}} (g : V ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ f) k)
    (hs : (g ≫ modificationSectionAtZero f b D.isIsoFibreAtZero) ≫ modificationProjection f b ≫
      f = g ≫ f) :
    chowPush C (pullback.fst (modificationProjectionAtInfinity f b) g ≫
          (modificationProjectionAtInfinity f b ≫ f)) (g ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) g)
        (pullbackSnd_comp_structureMorphism rfl g) ((k - 0) - p)
        ((Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
          (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q).idRule C
          (modificationProjectionAtInfinity f b ≫ f) (gysinSystemOfInvertible C)
          (pullback.fst (modificationProjectionAtInfinity f b) g) (k - 0)
          (D.bivariantClass.cap g k α)) ≍
      chowGroupCongr C hs (k - p)
        (q.idRule C (modificationProjection f b ≫ f) (gysinSystemOfInvertible C)
          (g ≫ modificationSectionAtZero f b D.isIsoFibreAtZero) k
          (chowGroupCongr C hs.symm k α)) := by
  have := D.properInclusionAtInfinity g
  have := D.properSectionAtZero g
  have e₂ : chowPush C (modificationInfinityBaseChangeOver f b g)
      (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
      (modificationInfinityBaseChange_over f b g) (k - 0) (D.bivariantClass.cap g k α) ≍
      chowPush C (g ≫ f) (modificationBaseChangeOver f b g)
        (modificationSectionAtZeroBaseChange f b D.isIsoFibreAtZero D.sectionAtZero_comp g)
        (modificationSectionAtZeroBaseChange_over f b g D.isIsoFibreAtZero D.sectionAtZero_comp)
        k α := by
    refine (heq_map_index (sub_zero k) (x := D.bivariantClass.cap g k α)
      (y := Eq.mp (congrArg (chowGroup C (modificationInfinityBaseChangeOver f b g))
        (sub_zero k)) (D.bivariantClass.cap g k α)) ?_ fun n x ↦
      chowPush C (modificationInfinityBaseChangeOver f b g)
        (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
        (modificationInfinityBaseChange_over f b g) n x).trans (heq_of_eq ?_)
    · rw [eq_mp_eq_cast]
      exact (cast_heq _ _).symm
    · exact D.pushforward_formula g k _ _ α
  refine (heq_of_eq ((congrArg (chowPush C
      (pullback.fst (modificationProjectionAtInfinity f b) g ≫
        (modificationProjectionAtInfinity f b ≫ f)) (g ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) g)
        (pullbackSnd_comp_structureMorphism rfl g) ((k - 0) - p))
      (chowCohomologyRestriction_idRule C _ (modificationInclusionAtInfinity f b) q
        (pullback.fst (modificationProjectionAtInfinity f b) g) (k - 0)
        (D.bivariantClass.cap g k α))).trans ?_)).trans ((heq_map_index (sub_zero k) e₂ fun n x ↦
    chowPush C (modificationBaseChangeOver f b g) (g ≫ f)
        (pullback.snd (modificationProjection f b) g) (modificationBaseChange_snd_over f b g)
        (n - p)
        (q.idRule C (modificationProjection f b ≫ f) (gysinSystemOfInvertible C)
          (pullback.fst (modificationProjection f b) g) n x)).trans (heq_of_eq ?_))
  · refine Eq.trans ?_ (congrArg (chowPush C (modificationBaseChangeOver f b g) (g ≫ f)
      (pullback.snd (modificationProjection f b) g) (modificationBaseChange_snd_over f b g)
      ((k - 0) - p)) (BivariantClass.idRule_chowPush_of_eq q
        (pullback.fst (modificationProjection f b) g) (modificationInfinityBaseChange f b g)
        (pullback.fst (modificationProjectionAtInfinity f b) g ≫
          modificationInclusionAtInfinity f b)
        (modificationInfinityBaseChange_comp_fst f b g) (modificationInfinityBaseChangeOver f b g)
        (by simp only [modificationInfinityBaseChangeOver, modificationProjectionAtInfinity,
          Category.assoc]) (modificationInfinityBaseChange_over f b g) (k - 0)
        (D.bivariantClass.cap g k α)).symm)
    exact (chowPush_comp C _ _ _ (modificationInfinityBaseChange f b g)
      (pullback.snd (modificationProjection f b) g) _
      (modificationInfinityBaseChange_comp_snd f b g) _ _ _ ((k - 0) - p) _).symm
  · rw [BivariantClass.idRule_chowPush_of_eq q (pullback.fst (modificationProjection f b) g)
      (modificationSectionAtZeroBaseChange f b D.isIsoFibreAtZero D.sectionAtZero_comp g)
      (g ≫ modificationSectionAtZero f b D.isIsoFibreAtZero) (pullback.lift_fst _ _ _) _ hs,
      chowPush_comp C _ _ _ _ (pullback.snd (modificationProjection f b) g) (𝟙 V)
        (modificationSectionAtZeroBaseChange_comp_snd f b g _ _) _ _ (Category.id_comp _),
      chowPush_id]

/-! ### Additivity and independence of `T` -/

/-- If `q ∈ A^p(W)` vanishes over `T ⊆ W_∞`, the restriction of `q|_{W_∞}` to `E` vanishes over
the base change of `T` to `E`. -/
private theorem vanishesOver_restriction_restriction_snd
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b)) :
    BivariantClass.VanishesOver
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjectionAtInfinity f b ≫ f)
        (pullback.fst (modificationProjectionAtInfinity f b) z) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
          (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q))
      (pullback.snd t (pullback.fst (modificationProjectionAtInfinity f b) z)) :=
  BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
    (hq.chowCohomologyRestriction_modificationInclusionAtInfinity t)

/-- The class `(q|_E)'` is additive in `q`. -/
theorem modificationExtension_add
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    {q₁ q₂ : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjection f b ≫ f) p}
    (hq₁ : BivariantClass.VanishesOver q₁ (t ≫ modificationInclusionAtInfinity f b))
    (hq₂ : BivariantClass.VanishesOver q₂ (t ≫ modificationInclusionAtInfinity f b)) :
    modificationExtension z t hT (hq₁.add hq₂) =
      modificationExtension z t hT hq₁ + modificationExtension z t hT hq₂ := by
  unfold modificationExtension
  exact closedCoverExtension_chowCohomologyRestriction_add C _ t _ _ (map_add _ q₁ q₂)
    (vanishesOver_restriction_restriction_snd z t hq₁)
    (vanishesOver_restriction_restriction_snd z t hq₂)
    (vanishesOver_restriction_restriction_snd z t (hq₁.add hq₂))

/-- The localized class is additive in `q`. -/
theorem localizedModificationClass_add
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    {q₁ q₂ : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjection f b ≫ f) p}
    (hq₁ : BivariantClass.VanishesOver q₁ (t ≫ modificationInclusionAtInfinity f b))
    (hq₂ : BivariantClass.VanishesOver q₂ (t ≫ modificationInclusionAtInfinity f b)) :
    localizedModificationClass D z t hT (hq₁.add hq₂) =
      localizedModificationClass D z t hT hq₁ + localizedModificationClass D z t hT hq₂ := by
  unfold localizedModificationClass
  rw [modificationExtension_add, ← bivariantCompositeBilinearOfInvertible_apply, map_add,
    AddMonoidHom.add_apply, bivariantCompositeBilinearOfInvertible_apply,
    bivariantCompositeBilinearOfInvertible_apply, BivariantClass.copy_add,
    bivariantProperPushforwardOfInvertible_add]

/-- **The localized class does not depend on `T`**, for a general class. Two closed subschemes
`T, T' ⊆ W_∞` containing every point of `W_∞` over `X ∖ Z`, over both of which `q` vanishes, give
the same localized class; for `q = P_p(Q)`, resp. `q = c_p(Q)`, this is the independence of
`P'_p(Q)`, resp. `c'_p(Q)`, of the choice of `T`. -/
@[stacks 0FAU "first assertion: P'_p(Q), resp. c'_p(Q), is independent of the closed subscheme \
T, for a general class q in place of P_p(Q), resp. c_p(Q)"]
theorem localizedModificationClass_eq {T' : Scheme.{u}} (t' : T' ⟶ modificationFibreAtInfinity f b)
    [IsClosedImmersion t']
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hT' : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t')
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (hq' : BivariantClass.VanishesOver q (t' ≫ modificationInclusionAtInfinity f b)) :
    localizedModificationClass D z t hT hq = localizedModificationClass D z t' hT' hq' := by
  have he : modificationExtension z t hT hq = modificationExtension z t' hT' hq' :=
    closedCoverExtension_eq_of_closedCover C (modificationProjectionAtInfinity f b ≫ f) t t'
      (pullback.fst (modificationProjectionAtInfinity f b) z) _ rfl
      (range_union_range_pullbackFst_eq_univ z t hT)
      (range_union_range_pullbackFst_eq_univ z t' hT')
      (vanishesOver_restriction_restriction_snd z t hq)
      (vanishesOver_restriction_restriction_snd z t' hq')
  unfold localizedModificationClass
  rw [he]

/-- **The generic form of Stacks 0F9K.** Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over
`𝐀¹_X`, with class `C ∈ A⁰(W_∞ ⟶ X)` of Stacks 0F9J, let `Z ⊆ X` and `T ⊆ W_∞` be closed with
`W_∞ = T ∪ E` for `E = W_∞ ×_X Z`, and let `q ∈ A^p(W)` vanish over `T`. Then the localized class
`q' = (E ⟶ Z)_* ∘ (q|_E)' ∘ C ∈ A^p(Z ⟶ X)` satisfies `(Z ⟶ X)_* ∘ q' = i_0^* q` in `A^p(X)`,
where `i_0^* q` is the restriction of `q` along the section at zero `i_0 : X ⟶ W`, read against
the structure morphism of `X` through `X ⟶ W ⟶ X = 𝟙 X`. -/
theorem properPushforwardChowCohomology_localizedModificationClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b)) :
    properPushforwardChowCohomology C f (z ≫ f) z rfl (localizedModificationClass D z t hT hq) =
      bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 X)
        (by rw [← Category.assoc, D.sectionAtZero_comp, Category.id_comp])
        (by rw [← Category.assoc, D.sectionAtZero_comp, Category.id_comp])
        (hv := Category.id_comp _) (hv' := Category.id_comp f) p
        (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
          (modificationProjection f b ≫ f) (modificationSectionAtZero f b D.isIsoFibreAtZero) p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q) := by
  refine BivariantClass.eq_of_idRule_eq C f _ _ _ fun {V} g _ k α ↦ ?_
  have hs : (g ≫ modificationSectionAtZero f b D.isIsoFibreAtZero) ≫
      modificationProjection f b ≫ f = g ≫ f := by
    rw [Category.assoc, ← Category.assoc (modificationSectionAtZero f b _),
      D.sectionAtZero_comp, Category.id_comp]
  rw [idRule_properPushforwardChowCohomology, BivariantClass.idRule_bivariantClassCongrBase,
    chowCohomologyRestriction_idRule, chowGroupCongr_chowGroupCongr]
  exact eq_of_heq ((chowPush_localizedModificationClass_cap_heq D z t hT hq g k α).trans
    (chowPush_idRule_bivariantClass_cap_heq D g k α hs))

end Modification

end Stacks.Chow

end
