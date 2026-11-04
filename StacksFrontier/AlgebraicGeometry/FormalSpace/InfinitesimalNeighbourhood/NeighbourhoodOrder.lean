module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.NeighbourhoodColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# The infinitesimal neighbourhoods are finite order thickenings of each other

Let `W` be a locally Noetherian formal algebraic space with reduction `i : W_red ⟶ W` and
infinitesimal neighbourhoods `W_0 ⊆ W_1 ⊆ ⋯`
(`AlgebraicGeometry.FormalSpace.reductionNeighbourhood`). For `n ≤ m` this file shows the two
remaining clauses of Stacks 0GHM:

* `W_n` is the `n`th infinitesimal neighbourhood of `W_0` inside `W_m`: over an affine object
  `T ⟶ W_m`, the base change `T ×_{W_m} W_n` is cut out by the `(n+1)`st power of the ideal of
  `T ×_{W_m} W_0`;
* the inclusion `W_n ⟶ W_m` is a finite order thickening: every base change of it along a
  scheme `T ⟶ W_m` is a closed immersion whose ideal sheaf has vanishing `(m+1)`st power.

## Main results

* `AlgebraicGeometry.FormalSpace.reductionNeighbourhood_isInfinitesimalNeighbourhood`: the
  first clause.
* `AlgebraicGeometry.FormalSpace.hasSchemePropertyULift_isNthOrderThickening_homOfLe`: the
  second clause.

## References

* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {W Wred : FppfSheaf B S hS} {i : Wred ⟶ W}

/-- Over affine objects, `W(h)(t) ∈ W_k` iff `h` kills `K(t)^(k+1)`. -/
theorem mem_reductionNeighbourhood_map_iff {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] {t : W.obj.obj (op T)}
    {K : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)} (hK : IsReductionIdeal i t K) (k : ℕ)
    {T' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] (h : T' ⟶ T) :
    W.obj.map h.op t ∈ (reductionNeighbourhood i k).obj (op T') ↔
      K ^ (k + 1) ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map h).appTop.hom := by
  rw [mem_reductionNeighbourhood_iff k (hK.map h), ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]

/-- A section of `W_m` comes from `W_n` iff it lies in `W_n`. -/
theorem exists_homOfLe_eq_iff {n m : ℕ} (hnm : n ≤ m) {T : BigFppfOver B S hS}
    (s : (reductionNeighbourhood i m).toFunctor.obj (op T)) :
    (∃ r, (Subfunctor.homOfLe (reductionNeighbourhood_mono i hnm)).app (op T) r = s) ↔
      s.1 ∈ (reductionNeighbourhood i n).obj (op T) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact r.2
  · intro hs
    exact ⟨⟨s.1, hs⟩, rfl⟩

/-- A section of `W_m` over an affine `T'` comes from `W_n` iff `K ^ (n + 1)` is killed, where `K`
is a reduction ideal of the section `t` of `W_m` over the affine `T`. -/
private theorem exists_homOfLe_eq_iff_pow_le_ker {n m : ℕ} (hnm : n ≤ m) {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (t : (reductionNeighbourhood i m).toFunctor.obj (op T))
    {K : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)} (hK : IsReductionIdeal i t.1 K)
    {T' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] (h : T' ⟶ T) :
    (∃ r, (Subfunctor.homOfLe (reductionNeighbourhood_mono i hnm)).app (op T') r =
        (reductionNeighbourhood i m).toFunctor.map h.op t) ↔
      K ^ (n + 1) ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map h).appTop.hom := by
  rw [exists_homOfLe_eq_iff hnm]
  exact mem_reductionNeighbourhood_map_iff hK n h

/-- **`W_n` is the `n`th infinitesimal neighbourhood of `W_0` in `W_m`** (Stacks 0GHM): for an
affine object `T`, a section `t ∈ W_m(T)` and the ideal `K` cutting out `T ×_{W_m} W_0` (read on
affine objects), the base change `T ×_{W_m} W_n` is cut out by `K^(n+1)`. -/
theorem reductionNeighbourhood_isInfinitesimalNeighbourhood (hred : IsReduction B S hS W Wred i)
    {n m : ℕ} (hnm : n ≤ m) {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (t : (reductionNeighbourhood i m).toFunctor.obj (op T))
    (K : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (hK : ∀ (T' : BigFppfOver B S hS) (h : T' ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T') →
      ((∃ r, (Subfunctor.homOfLe (reductionNeighbourhood_mono i (Nat.zero_le m))).app (op T') r =
          (reductionNeighbourhood i m).toFunctor.map h.op t) ↔
        K ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map h).appTop.hom))
    (T' : BigFppfOver B S hS) (h : T' ⟶ T) (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')) :
    (∃ r, (Subfunctor.homOfLe (reductionNeighbourhood_mono i hnm)).app (op T') r =
        (reductionNeighbourhood i m).toFunctor.map h.op t) ↔
      K ^ (n + 1) ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map h).appTop.hom := by
  obtain ⟨K', hK'⟩ := hred.exists_isReductionIdeal t.1
  have hKK' : K = K' := by
    refine ideal_eq_of_forall_le_ker_iff fun T'' h' hT'' => ?_
    have := hT''
    rw [← hK T'' h' hT'', ← pow_one K']
    exact exists_homOfLe_eq_iff_pow_le_ker (Nat.zero_le m) t hK' h'
  have := hT'
  rw [hKK']
  exact exists_homOfLe_eq_iff_pow_le_ker hnm t hK' h

/-- The inclusion `W_n ⟶ W_m` followed by `W_m ⟶ W` is the inclusion of `W_n`. -/
theorem homOfLe_comp_ι {n m : ℕ} (hnm : n ≤ m) :
    Subfunctor.homOfLe (reductionNeighbourhood_mono i hnm) ≫ (reductionNeighbourhood i m).ι =
      (reductionNeighbourhood i n).ι := rfl

/-- A pullback of `W_n ⟶ W_m` along `g : T ⟶ W_m` is a pullback of `W_n ⟶ W` along the composite
`T ⟶ W_m ⟶ W`, `W_m ⟶ W` being a monomorphism. -/
theorem isPullback_homOfLe_iff {n m : ℕ} (hnm : n ≤ m) {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (g : Q ⟶ (reductionNeighbourhood i m).toFunctor)
    (fst : P ⟶ (reductionNeighbourhood i n).toFunctor)
    (snd : P ⟶ Q) :
    IsPullback fst snd (Subfunctor.homOfLe (reductionNeighbourhood_mono i hnm)) g ↔
      IsPullback fst snd (reductionNeighbourhood i n).ι (g ≫ (reductionNeighbourhood i m).ι) := by
  have hbot : IsPullback g (𝟙 Q) (reductionNeighbourhood i m).ι
      (g ≫ (reductionNeighbourhood i m).ι) :=
    IsPullback.of_vert_isIso_mono ⟨(Category.id_comp _).symm⟩
  refine ⟨fun h => ?_, fun h => IsPullback.of_bot ?_ ?_ hbot⟩
  · have := h.paste_vert hbot
    rwa [Category.comp_id, homOfLe_comp_ι hnm] at this
  · rwa [Category.comp_id, homOfLe_comp_ι hnm]
  · apply (cancel_mono (reductionNeighbourhood i m).ι).1
    rw [Category.assoc, homOfLe_comp_ι hnm, h.w, Category.assoc]

/-- **The inclusion `W_n ⟶ W_m` is a finite order thickening** (Stacks 0GHM): every base change of
it along a scheme `T ⟶ W_m` is a closed immersion whose ideal sheaf has vanishing `(m+1)`st power.
-/
theorem hasSchemePropertyULift_isNthOrderThickening_homOfLe (hW : IsLocallyNoetherian B S hS W)
    (hred : IsReduction B S hS W Wred i) {n m : ℕ} (hnm : n ≤ m) :
    Space.HasSchemePropertyULift.{u + 1} B S hS
      (fun _ _ f => Stacks.Thickenings.IsNthOrderThickening m f)
      (Subfunctor.homOfLe (reductionNeighbourhood_mono i hnm)) := by
  classical
  let q := BigFppfOver.toScheme B S hS
  have hthick := isRepresentableThickeningULift_reductionNeighbourhood_ι hW hred n
  have hrep : uliftYoneda.{u + 1}.relativelyRepresentable
      (Subfunctor.homOfLe (reductionNeighbourhood_mono i hnm)) := by
    intro a g
    obtain ⟨b, snd, fst, h⟩ := hthick.rep (g ≫ (reductionNeighbourhood i m).ι)
    exact ⟨b, snd, fst, (isPullback_homOfLe_iff hnm g fst _).2 h⟩
  have hci : ∀ ⦃a b : BigFppfOver B S hS⦄ (g : uliftYoneda.{u + 1}.obj a ⟶
      (reductionNeighbourhood i m).toFunctor) (fst : uliftYoneda.{u + 1}.obj b ⟶
      (reductionNeighbourhood i n).toFunctor) (snd : b ⟶ a),
      IsPullback fst (uliftYoneda.map snd) (Subfunctor.homOfLe (reductionNeighbourhood_mono i hnm))
        g → _root_.AlgebraicGeometry.IsClosedImmersion (q.map snd) := fun a b g fst snd h =>
    (hthick.2 _ fst snd ((isPullback_homOfLe_iff hnm g fst _).1 h)).1
  refine ⟨hrep, fun a b g fst snd h => ⟨hci g fst snd h, ?_⟩⟩
  have := hci g fst snd h
  refine Scheme.ker_pow_eq_bot_of_forall_affineOpens _ fun V => ?_
  obtain ⟨ιV, hιV⟩ := Space.exists_openSiteObject'_hom a V.1
  let a₀ := Space.openSiteObject' a V.1
  have ha₀ : IsAffine (q.obj a₀) := V.2
  let g₀ := uliftYoneda.{u + 1}.map ιV ≫ g
  obtain ⟨b₀, snd₀, fst₀, h₀⟩ := hrep g₀
  have := hci g₀ fst₀ snd₀ h₀
  -- the square over the affine open
  have hsqSite : IsPullback (uliftYoneda.preimage (h.lift fst₀
      (uliftYoneda.map snd₀ ≫ uliftYoneda.map ιV) (by rw [h₀.w, Category.assoc])))
      snd₀ snd ιV := by
    refine IsPullback.of_map_of_faithful uliftYoneda.{u + 1} ?_
    rw [uliftYoneda.map_preimage]
    exact IsPullback.of_right' h₀ h
  have hsqScheme := (hsqSite.map q).flip
  rw [hιV] at hsqScheme
  refine ⟨_, q.map snd₀, _, hsqScheme, ?_⟩
  -- the ideal of `b₀` in `a₀` is `K ^ (n + 1)`, for `K` the ideal of the reduction
  let t : (reductionNeighbourhood i m).toFunctor.obj (op a₀) := uliftYonedaEquiv g₀
  obtain ⟨K, hK⟩ := hred.exists_isReductionIdeal t.1
  have hKm : K ^ (m + 1) = ⊥ := (mem_reductionNeighbourhood_iff m hK).1 t.2
  have hker : RingHom.ker (q.map snd₀).appTop.hom = K ^ (n + 1) := by
    refine ideal_eq_of_forall_le_ker_iff fun T' h' hT' => ?_
    have := hT'
    rw [← Scheme.exists_factor_iff_ker_appTop_le,
      ← exists_homOfLe_eq_iff_pow_le_ker hnm t hK h']
    constructor
    · rintro ⟨l, hl⟩
      obtain ⟨l₀, hl₀⟩ := exists_siteHom_of_toScheme_comp_eq snd₀ h' l hl
      refine ⟨uliftYonedaEquiv (uliftYoneda.map l₀ ≫ fst₀), ?_⟩
      rw [← uliftYonedaEquiv_comp, Category.assoc, h₀.w, ← Category.assoc,
        ← Functor.map_comp, hl₀, uliftYonedaEquiv_naturality]
      rfl
    · rintro ⟨r, hr⟩
      have hw : uliftYonedaEquiv.symm r ≫ Subfunctor.homOfLe (reductionNeighbourhood_mono i hnm) =
          uliftYoneda.map h' ≫ g₀ := by
        rw [uliftYonedaEquiv_symm_comp, hr]
        apply uliftYonedaEquiv.injective
        rw [Equiv.apply_symm_apply, uliftYonedaEquiv_naturality]
        rfl
      let l := h₀.lift _ _ hw
      refine ⟨q.map (uliftYoneda.preimage l), ?_⟩
      rw [← Functor.map_comp]
      congr 1
      apply uliftYoneda.map_injective
      rw [Functor.map_comp, uliftYoneda.map_preimage]
      exact h₀.lift_snd _ _ _
  rw [hker, ← pow_mul, eq_bot_iff, ← hKm]
  exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left _ n.succ_pos)

end AlgebraicGeometry.FormalSpace

end
