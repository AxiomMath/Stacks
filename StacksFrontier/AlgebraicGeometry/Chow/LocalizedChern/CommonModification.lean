module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinAtInfinityClassProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseTensor
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Preparation

/-!
# A common modification of two modifications of the projective line

Let `X` be a scheme over `S` and let `b_i : W_i ⟶ 𝐏¹_X`, `i = 1, 2`, be morphisms which are
isomorphisms over the affine chart `𝐀¹_X`. The fibre product `W = W_1 ×_{𝐏¹_X} W_2`, with its
projections `g_i : W ⟶ W_i` and `b = b_1 ∘ g_1 = b_2 ∘ g_2`, is again an isomorphism over `𝐀¹_X`,
and so are `g_1` and `g_2` over `b_1^{-1}(𝐀¹_X)` and `b_2^{-1}(𝐀¹_X)`; when the `b_i` are proper,
so are the `g_i` and `b`.

The data of Stacks 0F9K attached to a modification pull back along any morphism of modifications
`g : W' ⟶ W` with `b' = b ∘ g`. If `Q ∈ D(𝒪_W)` and `T ⊆ W_∞` is closed, contains every point of
`W_∞` lying over `X ∖ Z` and `Q|_T` is zero, then `T' = W'_∞ ×_W T`, the inverse image of `T` in
`W'_∞`, contains every point of `W'_∞` lying over `X ∖ Z`, and `(Lg^*Q)|_{T'}` is zero. If moreover
the restriction of `Q` to `b^{-1}(𝐀¹_X)` is the pullback of an object `F ∈ D(𝒪_X)`, then the
restriction of `Lg^*Q` to `(b')^{-1}(𝐀¹_X)` is the pullback of `F` too.

## Main results

* `Stacks.Chow.isIso_pullbackSnd_pullbackFst_pullbackFst`,
  `Stacks.Chow.isIso_pullbackSnd_pullbackSnd_pullbackFst` — the projections `g_i` of the fibre
  product are isomorphisms over `b_i^{-1}(𝐀¹)`.
* `Stacks.Chow.isIso_pullbackSnd_pullbackFst_comp_projectiveLineAffineChart` — the fibre product
  `W_1 ×_{𝐏¹_X} W_2` is an isomorphism over `𝐀¹_X`.
* `Stacks.Chow.mem_range_pullbackSnd_of_notMem_range` — the inverse image of `T` in `W'_∞`
  contains every point of `W'_∞` lying over `X ∖ Z`.
* `Stacks.Chow.isZero_derivedPullback_derivedPullback_pullbackSnd` — `(Lg^*Q)` restricts to zero
  on the inverse image of `T`.
* `Stacks.Chow.nonempty_derivedPullback_affineChart_derivedPullback_iso` — the restriction of
  `Lg^*Q` to `(b')^{-1}(𝐀¹_X)` is the pullback of `F`.

## Implementation notes

That a morphism `b : W ⟶ 𝐏¹_X` is an isomorphism over `𝐀¹_X` is expressed as
`IsIso (pullback.snd b (projectiveLineAffineChart f))`, and that `g : W' ⟶ W` is an isomorphism
over `b^{-1}(𝐀¹_X)` as `IsIso (pullback.snd g (pullback.fst b (projectiveLineAffineChart f)))`.
In the pullback lemmas `b'` is any morphism with `g ≫ b = b'`, and the inverse image of `T` is the
fibre product of `T ⟶ W_∞ ⟶ W` and `W'_∞ ⟶ W' ⟶ W`.

## References

* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0FE8](https://stacks.math.columbia.edu/tag/0FE8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The fibre product of two modifications -/

section FibreProduct

variable {𝒞 : Type*} [Category 𝒞] [HasPullbacks 𝒞] {P A W₁ W₂ : 𝒞} (b₁ : W₁ ⟶ P)
  (b₂ : W₂ ⟶ P) (j : A ⟶ P)

/-- **The first projection of `W₁ ×_P W₂` is an isomorphism over `b₁⁻¹(A)`** when `b₂` is an
isomorphism over `A`: the base change of `pullback.fst b₁ b₂` along `b₁⁻¹(A) ⟶ W₁` is an
isomorphism. -/
theorem isIso_pullbackSnd_pullbackFst_pullbackFst [IsIso (pullback.snd b₂ j)] :
    IsIso (pullback.snd (pullback.fst b₁ b₂) (pullback.fst b₁ j)) := by
  have hc : pullback.fst b₁ j ≫ b₁ =
      (pullback.snd b₁ j ≫ inv (pullback.snd b₂ j) ≫ pullback.fst b₂ j) ≫ b₂ := by
    simp [pullback.condition]
  let φ : pullback b₁ j ⟶ pullback b₁ b₂ := pullback.lift _ _ hc
  have hφ : φ ≫ pullback.fst b₁ b₂ = pullback.fst b₁ j := pullback.lift_fst _ _ _
  let ψ : pullback b₁ j ⟶ pullback (pullback.fst b₁ b₂) (pullback.fst b₁ j) :=
    pullback.lift φ (𝟙 _) (by rw [hφ, Category.id_comp])
  refine ⟨ψ, ?_, pullback.lift_snd _ _ _⟩
  have hu : (pullback.fst (pullback.fst b₁ b₂) (pullback.fst b₁ j) ≫ pullback.snd b₁ b₂) ≫ b₂ =
      (pullback.snd (pullback.fst b₁ b₂) (pullback.fst b₁ j) ≫ pullback.snd b₁ j) ≫ j := by
    rw [Category.assoc, Category.assoc, ← pullback.condition (f := b₁) (g := b₂),
      pullback.condition_assoc, pullback.condition (f := b₁) (g := j)]
  have hv : pullback.snd (pullback.fst b₁ b₂) (pullback.fst b₁ j) ≫ pullback.snd b₁ j ≫
      inv (pullback.snd b₂ j) = pullback.lift _ _ hu := by
    rw [← Category.assoc, IsIso.comp_inv_eq, pullback.lift_snd]
  have hφ' : pullback.snd (pullback.fst b₁ b₂) (pullback.fst b₁ j) ≫ φ =
      pullback.fst (pullback.fst b₁ b₂) (pullback.fst b₁ j) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hφ, ← pullback.condition]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc (pullback.snd b₁ j),
        ← Category.assoc, hv, pullback.lift_fst]
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, hφ', Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]

/-- **The second projection of `W₁ ×_P W₂` is an isomorphism over `b₂⁻¹(A)`** when `b₁` is an
isomorphism over `A`: the base change of `pullback.snd b₁ b₂` along `b₂⁻¹(A) ⟶ W₂` is an
isomorphism. -/
theorem isIso_pullbackSnd_pullbackSnd_pullbackFst [IsIso (pullback.snd b₁ j)] :
    IsIso (pullback.snd (pullback.snd b₁ b₂) (pullback.fst b₂ j)) := by
  have h := isIso_pullbackSnd_pullbackFst_pullbackFst b₂ b₁ j
  have hsq := (IsPullback.of_hasPullback (pullback.fst b₂ b₁) (pullback.fst b₂ j)).of_iso
    (fst' := pullback.fst (pullback.fst b₂ b₁) (pullback.fst b₂ j) ≫ (pullbackSymmetry b₂ b₁).hom)
    (snd' := pullback.snd (pullback.fst b₂ b₁) (pullback.fst b₂ j))
    (f' := pullback.snd b₁ b₂) (g' := pullback.fst b₂ j) (Iso.refl _) (pullbackSymmetry b₂ b₁)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  rw [← hsq.isoPullback_hom_snd] at h
  exact IsIso.of_isIso_comp_left hsq.isoPullback.hom _

end FibreProduct

section Modification

variable {X S W₁ W₂ : Scheme.{u}} (f : X ⟶ S) (b₁ : W₁ ⟶ projectiveLineProduct f)
  (b₂ : W₂ ⟶ projectiveLineProduct f)

/-- **The fibre product of two modifications is a modification**: if `b₁ : W₁ ⟶ 𝐏¹_X` and
`b₂ : W₂ ⟶ 𝐏¹_X` are isomorphisms over `𝐀¹_X`, then so is `b₁ ∘ g₁ : W₁ ×_{𝐏¹_X} W₂ ⟶ 𝐏¹_X`. -/
theorem isIso_pullbackSnd_pullbackFst_comp_projectiveLineAffineChart
    (hA₁ : IsIso (pullback.snd b₁ (projectiveLineAffineChart f)))
    (hA₂ : IsIso (pullback.snd b₂ (projectiveLineAffineChart f))) :
    IsIso (pullback.snd (pullback.fst b₁ b₂ ≫ b₁) (projectiveLineAffineChart f)) :=
  isIso_pullbackSnd_comp_projectiveLineAffineChart f b₁ _ hA₁
    (isIso_pullbackSnd_pullbackFst_pullbackFst b₁ b₂ _)

end Modification

/-! ### Pulling back the data of Stacks 0F9K along a morphism of modifications -/

section PullbackData

variable {X S W W' Z T : Scheme.{u}} (f : X ⟶ S) {b : W ⟶ projectiveLineProduct f}
  {b' : W' ⟶ projectiveLineProduct f} (g : W' ⟶ W) (hb : g ≫ b = b') (z : Z ⟶ X)
  (t : T ⟶ modificationFibreAtInfinity f b)

include hb in
/-- **The inverse image of `T` contains the points of `W'_∞` over `X ∖ Z`.** Let `g : W' ⟶ W`
with `b' = b ∘ g`, and let `T ⟶ W_∞` contain every point of `W_∞` lying over `X ∖ Z`. Then the
inverse image `W'_∞ ×_W T` of `T` in `W'_∞` contains every point of `W'_∞` lying over `X ∖ Z`. -/
theorem mem_range_pullbackSnd_of_notMem_range
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (w' : modificationFibreAtInfinity f b')
    (hw' : modificationProjectionAtInfinity f b' w' ∉ Set.range z) :
    w' ∈ Set.range (pullback.snd (t ≫ modificationInclusionAtInfinity f b)
      (modificationInclusionAtInfinity f b' ≫ g)) := by
  subst hb
  rw [Scheme.Pullback.range_snd]
  have hinf : g (modificationInclusionAtInfinity f (g ≫ b) w') ∈
      Set.range (modificationInclusionAtInfinity f b) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨pullback.snd (g ≫ b) (infinitySection f) w', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
  obtain ⟨w, hw⟩ := hinf
  have hproj : modificationProjectionAtInfinity f b w =
      modificationProjectionAtInfinity f (g ≫ b) w' := by
    simp only [modificationProjectionAtInfinity, modificationProjection, Scheme.Hom.comp_apply, hw]
  obtain ⟨s, hs⟩ := hT w (hproj ▸ hw')
  exact ⟨s, by rw [Scheme.Hom.comp_apply, hs, hw, Scheme.Hom.comp_apply]⟩

include hb in
/-- **`Lg^*Q` restricts to zero on the inverse image of `T`.** Let `g : W' ⟶ W` with
`b' = b ∘ g`, and let `Q ∈ D(𝒪_W)` restrict to zero on `T ⟶ W_∞ ⟶ W`. Then `Lg^*Q` restricts to
zero on `W'_∞ ×_W T ⟶ W'_∞ ⟶ W'`. -/
theorem isZero_derivedPullback_derivedPullback_pullbackSnd {Q : DerivedCategory W.Modules}
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd (t ≫ modificationInclusionAtInfinity f b)
        (modificationInclusionAtInfinity f b' ≫ g) ≫
          modificationInclusionAtInfinity f b').toLRSHom.toShHom).obj
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj
        Q)) := by
  refine isZero_derivedPullback_of_isZero_of_comp_eq (a := pullback.fst _ _) ?_ hzero
  rw [Category.assoc, ← pullback.condition]

/-- **Restriction of an identification with a pullback along a commutative square.** Let
`u : V ⟶ W`, `v : V ⟶ X`, and let `Lu^*Q ≅ Lv^*F`. If `m : V' ⟶ V` satisfies `m ≫ u = u' ≫ g`
and `m ≫ v = v'`, then `Lu'^*(Lg^*Q) ≅ Lv'^*F`. -/
theorem nonempty_derivedPullback_derivedPullback_iso_of_comp_eq {V V' W W' X : Scheme.{u}}
    {u : V ⟶ W} {v : V ⟶ X} {u' : V' ⟶ W'} {v' : V' ⟶ X} (g : W' ⟶ W) (m : V' ⟶ V)
    (hu : m ≫ u = u' ≫ g) (hv : m ≫ v = v') {Q : DerivedCategory W.Modules}
    {F : DerivedCategory X.Modules}
    (e : Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        u.toLRSHom.toShHom).obj Q ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback v.toLRSHom.toShHom).obj F)) :
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        u'.toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj
            Q) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback v'.toLRSHom.toShHom).obj F) := by
  obtain ⟨e⟩ := e
  subst hv
  have hu' : (u' ≫ g).toLRSHom.toShHom = (m ≫ u).toLRSHom.toShHom := by rw [hu]
  exact ⟨derivedPullbackCompIsoOfScheme u' g Q ≪≫
    (eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq hu')).app Q ≪≫
    (derivedPullbackCompIsoOfScheme m u Q).symm ≪≫
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback m.toLRSHom.toShHom).mapIso e ≪≫
    derivedPullbackCompIsoOfScheme m v F⟩

include hb in
/-- **The restriction of `Lg^*Q` to `(b')^{-1}(𝐀¹_X)` is the pullback of `F`** when that of `Q`
to `b^{-1}(𝐀¹_X)` is, for `g : W' ⟶ W` with `b' = b ∘ g`. -/
theorem nonempty_derivedPullback_affineChart_derivedPullback_iso {Q : DerivedCategory W.Modules}
    {F : DerivedCategory X.Modules}
    (e : Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst b (projectiveLineAffineChart f)).toLRSHom.toShHom).obj Q ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst b (projectiveLineAffineChart f) ≫
          modificationProjection f b).toLRSHom.toShHom).obj F)) :
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst b' (projectiveLineAffineChart f)).toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj
            Q) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst b' (projectiveLineAffineChart f) ≫
          modificationProjection f b').toLRSHom.toShHom).obj F) := by
  have hc : (pullback.fst b' (projectiveLineAffineChart f) ≫ g) ≫ b =
      pullback.snd b' (projectiveLineAffineChart f) ≫ projectiveLineAffineChart f := by
    rw [Category.assoc, hb, pullback.condition]
  refine nonempty_derivedPullback_derivedPullback_iso_of_comp_eq g (pullback.lift _ _ hc)
    (pullback.lift_fst _ _ _) ?_ e
  rw [← Category.assoc, pullback.lift_fst, Category.assoc, ← hb]
  rfl

end PullbackData

end Stacks.Chow

end
