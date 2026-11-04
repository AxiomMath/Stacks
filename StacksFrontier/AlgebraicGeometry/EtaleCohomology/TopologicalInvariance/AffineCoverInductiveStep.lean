module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyCAffine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineCase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Coproduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SectionComplement

/-!
# The inductive step of the affine case of topological invariance

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineCase` reduces the
essential surjectivity of base change along a universal homeomorphism to the affine case
`Stacks.Etale.EssSurjAffineEtalePullback`, and reduces that in turn to the single inductive step
of the second proof of Stacks Project, Tag 04DZ, the base case being proved there. This file
performs the *geometric* half of that step, so that what remains of the affine case — and hence
of Tag 04DZ and of Tag 04E0 — is one descent statement.

The step. Let `f : X ⟶ Y` be a universal homeomorphism of affine schemes and let `p : U ⟶ X` be
étale with `U` affine and with fibre degrees bounded by `n + 1`. Stacks Project, Tag 04DW in the
affine form `Stacks.EtaleCohomology.exists_affine_etale_surjective_pullback` produces an affine
`W` étale over `Y` together with a surjection `k : W_X ⟶ U` over `X`, where `W_X = W ×_Y X`. The
base change `U ×_X W_X ⟶ W_X` of `p` is then étale with an affine source, and `k` is a section
of it; by Stacks Project, Tag 024T that section is an open and closed immersion, so
`U ×_X W_X` is the disjoint union of `W_X` and of the complement `R` of the section. The
complement has fibre degrees bounded by `n`, by
`AlgebraicGeometry.boundsFiberDegrees_sectionComplement`, so the inductive hypothesis applies to
it over the universal homeomorphism `W_X ⟶ W` and produces an affine `V'` étale over `W` with
`V' ×_W W_X ≅ R`. Then `V'' = W ⨿ V'` is affine, étale over `W`, and its base change to `W_X` is
`W_X ⨿ R ≅ U ×_X W_X`: a binary coproduct of schemes stays a binary coproduct after base change,
because the category of schemes is finitary extensive.

What is *not* done here is the descent of `V''` from `W` down to `Y`, which is the last paragraph
of the source's proof; it is carried as the hypothesis
`Stacks.Etale.EtaleDescentAlongAffineCover`.

## Main definitions

* `Stacks.Etale.EtaleDescentAlongAffineCover` — the descent statement the step still needs: if
  a scheme `U` étale over `X` lies over the image of an affine `W` étale over `Y`, and the base
  change of `U` to `W_X` is the base change of a scheme `V''` étale over `W`, then `U` is itself
  the base change of a scheme étale over `Y`.

## Main results

* `Stacks.Etale.isPullback_of_fst_snd` — a pullback square along `α ≫ v` exhibits its comparison
  morphism to the pullback along `v` as a base change of `α`.
* `Stacks.Etale.exists_affine_etale_coproduct_pullback_iso` — **the geometric half of the step.**
  The scheme `V''` étale over `W` whose base change to `W_X` is `U ×_X W_X`.
* `Stacks.Etale.essSurjAffineEtalePullbackBounded_succ` — the inductive step, granted the descent
  statement.
* `Stacks.Etale.essSurjAffineEtalePullback_of_etaleDescentAlongAffineCover` — consequently the
  affine case, and with it Stacks Project, Tags 04DZ and 04E0, follows from the descent statement
  alone.
* `Stacks.Etale.etalePullback_isEquivalence_of_etaleDescentAlongAffineCover` — and so does the
  whole equivalence of small étale sites.

## Implementation notes

The fibre product of `W` with `f` is written `pullback w f`, so that its projection to `W` is
`CategoryTheory.Limits.pullback.fst` and its projection to `X` is
`CategoryTheory.Limits.pullback.snd`; Tag 04DW is stated in this library for `pullback f w`, and
the two are compared by `CategoryTheory.Limits.pullbackSymmetry` once, at the point of use.

The decomposition of the base change of a coproduct is obtained from
`CategoryTheory.FinitaryExtensive` through `CategoryTheory.Limits.BinaryCofan.isVanKampen_iff`,
rather than by computing the two open subschemes of `V'' ×_W W_X` and showing them
complementary: the van Kampen property delivers the colimit from exactly the two Cartesian
squares which `Stacks.Etale.isPullback_of_fst_snd` provides, and the resulting
`CategoryTheory.Limits.IsColimit` is also what pins the isomorphism down on each summand.

The affineness of the descended scheme is not asked of the carried hypothesis: it is recovered
from `Stacks.Etale.isAffine_of_isAffine_pullback`, as in
`Stacks.Etale.essSurjAffineEtalePullback_of_exists_etale_pullback_iso`.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04E0](https://stacks.math.columbia.edu/tag/04E0)
* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 024T](https://stacks.math.columbia.edu/tag/024T)
* [Stacks Project, Tag 03WU](https://stacks.math.columbia.edu/tag/03WU)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

/-! ### Base change along a morphism into the first factor -/

/-- **A change of the first factor of a fibre product is a base change.** Let `α : A ⟶ V`,
`v : V ⟶ W` and `g : Z ⟶ W` be morphisms of schemes and let `P` be the fibre product of `α ≫ v`
with `g`. The comparison morphism `m : P ⟶ V ×_W Z`, characterized by its two components,
exhibits `P` as the base change of `V ×_W Z` along `α`. -/
theorem isPullback_of_fst_snd {A V W Z P : Scheme.{u}} {α : A ⟶ V} {v : V ⟶ W} {g : Z ⟶ W}
    {π₁ : P ⟶ A} {π₂ : P ⟶ Z} (hP : IsPullback π₁ π₂ (α ≫ v) g)
    (m : P ⟶ pullback v g) (hm₁ : m ≫ pullback.fst v g = π₁ ≫ α)
    (hm₂ : m ≫ pullback.snd v g = π₂) :
    IsPullback m π₁ (pullback.fst v g) α := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hm₁ ?_ ?_ ?_ ?_)
  · exact fun t ↦ hP.lift t.snd (t.fst ≫ pullback.snd v g) (by
      rw [← Category.assoc, ← t.condition, Category.assoc, pullback.condition, Category.assoc])
  · intro t
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hm₁, ← Category.assoc, hP.lift_fst, t.condition]
    · rw [Category.assoc, hm₂, hP.lift_snd]
  · intro t
    exact hP.lift_fst _ _ _
  · intro t l hl₁ hl₂
    refine hP.hom_ext ?_ ?_
    · rw [hl₂, hP.lift_fst]
    · rw [hP.lift_snd, ← hm₂, ← Category.assoc, hl₁]

/-! ### The descent statement the step still needs -/

/-- **Descent of an étale scheme along an affine étale cover of the target.** Let `f : X ⟶ Y` be
a universal homeomorphism of affine schemes, let `w : W ⟶ Y` be étale with `W` affine, and write
`W_X = W ×_Y X` for the base change of `X`. Let `p : U ⟶ X` be étale with `U` affine, lying over
the image of `W_X` in `X`, and suppose that the base change `U ×_X W_X` of `U` is, over `W_X`,
the base change of a scheme `V''` étale over `W` with `V''` affine. Then `U` is, over `X`, the
base change along `f` of a scheme étale over `Y`.

This is the last paragraph of the second proof of Stacks Project, Tag 04DZ. There the
identification over `W ×_Y W` of the two base changes of `V''` is produced by full faithfulness
of base change along the universal homeomorphism over `W ×_Y W` — in this library
`Stacks.Etale.bijective_baseChange_hom_of_universalHomeomorphism`, which needs no affineness —
and is a descent datum for `V''` relative to `W/Y`, the cocycle condition following from the
uniqueness of that identification over `W ×_Y W ×_Y W`; the datum is effective by effectivity of
affine descent, Stacks Project, Tag 0245, in this library
`AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom`, which is the one-member form the
descent datum here is in.

The clause that `U` lie over the image of `W_X` is what makes `{W ⟶ Y}` an fpqc covering of the
open subscheme of `Y` over which the descent takes place: `w` is étale, hence open, but it need
not be surjective, whereas Tag 0245 asks for a covering family. That localization is performed in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineDescentFpqc`, so this
statement follows from `Stacks.Etale.EtaleDescentAlongFpqcAffineCover`, where `w` is surjective
and no affineness of the base remains. -/
def EtaleDescentAlongAffineCover : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), UniversalHomeomorphism f → IsAffine X → IsAffine Y →
    ∀ (W : Scheme.{u}) (w : W ⟶ Y), Etale w → IsAffine W →
      ∀ (U : Scheme.{u}) (p : U ⟶ X), Etale p → IsAffine U →
        Set.range p.base ⊆ Set.range (pullback.snd w f).base →
        ∀ (V'' : Scheme.{u}) (v'' : V'' ⟶ W), Etale v'' → IsAffine V'' →
          ∀ e : pullback v'' (pullback.fst w f) ≅ pullback p (pullback.snd w f),
            e.hom ≫ pullback.snd p (pullback.snd w f) =
              pullback.snd v'' (pullback.fst w f) →
            ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (eU : pullback q f ≅ U),
              eU.hom ≫ p = pullback.snd q f

/-! ### The geometric half of the inductive step -/

/-- **The scheme étale over `W` whose base change to `W_X` is `U ×_X W_X`.** Let `f : X ⟶ Y` be a
universal homeomorphism of affine schemes, let `w : W ⟶ Y` be étale with `W` affine, let
`p : U ⟶ X` be étale with `U` affine and with fibre degrees bounded by `n + 1`, and let
`k : W_X ⟶ U` be a morphism over `X`, where `W_X = W ×_Y X`. Granted the affine case for the
bound `n`, there is an affine scheme `V''` étale over `W` together with an isomorphism
`V'' ×_W W_X ≅ U ×_X W_X` over `W_X`.

This is the construction in the middle of the second proof of Stacks Project, Tag 04DZ. The
base change `U ×_X W_X ⟶ W_X` of `p` is étale and `k` makes it admit a section, which by Stacks
Project, Tag 024T is an open and closed immersion; the complement `R` of that section has fibre
degrees bounded by `n`, by `AlgebraicGeometry.boundsFiberDegrees_sectionComplement`, so the
affine case for `n` applied to the universal homeomorphism `W_X ⟶ W` descends it to an affine
`V'` étale over `W`. Then `V'' = W ⨿ V'`, and the identification of its base change is the
statement that a binary coproduct of schemes remains one after base change, which is the van
Kampen property of `CategoryTheory.FinitaryExtensive`. -/
theorem exists_affine_etale_coproduct_pullback_iso {n : ℕ}
    (ih : EssSurjAffineEtalePullbackBounded.{u} n) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] [IsAffine X] [IsAffine Y] {W : Scheme.{u}} (w : W ⟶ Y)
    (hw : Etale w) (hWaff : IsAffine W) {U : Scheme.{u}} (p : U ⟶ X) (hp : Etale p)
    (hU : IsAffine U) (hdeg : BoundsFiberDegrees p ((n + 1 : ℕ) : ℤ))
    (k : (pullback w f : Scheme.{u}) ⟶ U) (hk : k ≫ p = pullback.snd w f) :
    ∃ (V'' : Scheme.{u}) (v'' : V'' ⟶ W) (_ : Etale v'') (_ : IsAffine V'')
      (e : pullback v'' (pullback.fst w f) ≅ pullback p (pullback.snd w f)),
      e.hom ≫ pullback.snd p (pullback.snd w f) = pullback.snd v'' (pullback.fst w f) := by
  have _ : Etale w := hw
  -- the base change `W_X ⟶ W` of `f` is a universal homeomorphism of affine schemes
  have hfW : UniversalHomeomorphism (pullback.fst w f) := by
    rw [universalHomeomorphism_iff]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback w f).flip ((universalHomeomorphism_iff f).mp inferInstance)
  -- the base change of `p` to `W_X`, and the section of it given by `k`
  have _ : Etale (pullback.snd p (pullback.snd w f)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback p (pullback.snd w f)) hp
  obtain ⟨s, hs⟩ : ∃ s : (pullback w f : Scheme.{u}) ⟶ (pullback p (pullback.snd w f)),
      s ≫ pullback.snd p (pullback.snd w f) = 𝟙 _ :=
    ⟨pullback.lift k (𝟙 _) (by rwa [Category.id_comp]), pullback.lift_snd _ _ _⟩
  have _ : IsOpenImmersion s := isOpenImmersion_of_isSection _ s hs
  -- the complement of the section, with its fibre degrees bounded by `n`
  have hRaff : IsAffine (sectionComplement (pullback.snd p (pullback.snd w f)) s hs).toScheme :=
    isAffine_sectionComplement _ s hs
  have hdegR : BoundsFiberDegrees
      ((sectionComplement (pullback.snd p (pullback.snd w f)) s hs).ι ≫
        pullback.snd p (pullback.snd w f)) ((n : ℕ) : ℤ) :=
    boundsFiberDegrees_sectionComplement _ s hs n
      (boundsFiberDegrees_of_isPullback (IsPullback.of_hasPullback p (pullback.snd w f)) hdeg)
  -- the affine case for the bound `n`, applied to the complement over `W_X ⟶ W`
  obtain ⟨V', q', hq', hV'aff, e', he'⟩ := ih (pullback.fst w f) hfW inferInstance hWaff
    (sectionComplement (pullback.snd p (pullback.snd w f)) s hs).toScheme
    ((sectionComplement (pullback.snd p (pullback.snd w f)) s hs).ι ≫
      pullback.snd p (pullback.snd w f)) inferInstance hRaff hdegR
  -- the two summands of `V'' = W ⨿ V'`
  have hinl : (coprod.inl : W ⟶ (W ⨿ V' : Scheme.{u})) ≫ coprod.desc (𝟙 W) q' = 𝟙 W :=
    coprod.inl_desc _ _
  have hinr : (coprod.inr : V' ⟶ (W ⨿ V' : Scheme.{u})) ≫ coprod.desc (𝟙 W) q' = q' :=
    coprod.inr_desc _ _
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a : (pullback w f : Scheme.{u}) ⟶
      pullback (coprod.desc (𝟙 W) q') (pullback.fst w f),
      a ≫ pullback.fst (coprod.desc (𝟙 W) q') (pullback.fst w f) =
          pullback.fst w f ≫ coprod.inl ∧
        a ≫ pullback.snd (coprod.desc (𝟙 W) q') (pullback.fst w f) = 𝟙 _ :=
    ⟨pullback.lift (pullback.fst w f ≫ coprod.inl) (𝟙 _)
      (by rw [Category.assoc, hinl, Category.comp_id, Category.id_comp]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b : (sectionComplement (pullback.snd p (pullback.snd w f)) s hs).toScheme
      ⟶ pullback (coprod.desc (𝟙 W) q') (pullback.fst w f),
      b ≫ pullback.fst (coprod.desc (𝟙 W) q') (pullback.fst w f) =
          (e'.inv ≫ pullback.fst q' (pullback.fst w f)) ≫ coprod.inr ∧
        b ≫ pullback.snd (coprod.desc (𝟙 W) q') (pullback.fst w f) =
          e'.inv ≫ pullback.snd q' (pullback.fst w f) :=
    ⟨pullback.lift ((e'.inv ≫ pullback.fst q' (pullback.fst w f)) ≫ coprod.inr)
      (e'.inv ≫ pullback.snd q' (pullback.fst w f))
      (by simp only [Category.assoc, hinr]; rw [pullback.condition]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- the two summands pull back to the two Cartesian squares the van Kampen property wants
  have hP₁ : IsPullback (pullback.fst w f) (𝟙 (pullback w f : Scheme.{u}))
      ((coprod.inl : W ⟶ (W ⨿ V' : Scheme.{u})) ≫ coprod.desc (𝟙 W) q') (pullback.fst w f) := by
    rw [hinl]
    exact (IsPullback.of_horiz_isIso (CommSq.mk (by simp))).flip
  have hP₂ : IsPullback (e'.inv ≫ pullback.fst q' (pullback.fst w f))
      (e'.inv ≫ pullback.snd q' (pullback.fst w f))
      ((coprod.inr : V' ⟶ (W ⨿ V' : Scheme.{u})) ≫ coprod.desc (𝟙 W) q')
      (pullback.fst w f) := by
    rw [hinr]
    exact IsPullback.of_iso_pullback
      (CommSq.mk (by simp only [Category.assoc]; rw [pullback.condition])) e'.symm rfl rfl
  have sq₁ := isPullback_of_fst_snd hP₁ a ha₁ ha₂
  have sq₂ := isPullback_of_fst_snd hP₂ b hb₁ hb₂
  -- the base change of the coproduct is the coproduct of the base changes
  obtain ⟨hcolA⟩ := ((BinaryCofan.isVanKampen_iff
      (BinaryCofan.mk (coprod.inl : W ⟶ (W ⨿ V' : Scheme.{u}))
        (coprod.inr : V' ⟶ (W ⨿ V' : Scheme.{u})))).mp
      (FinitaryExtensive.vanKampen _ (coprodIsCoprod W V'))
      (BinaryCofan.mk a b) (pullback.fst w f)
      (e'.inv ≫ pullback.fst q' (pullback.fst w f))
      (pullback.fst (coprod.desc (𝟙 W) q') (pullback.fst w f))
      ha₁.symm hb₁.symm).mpr ⟨sq₁, sq₂⟩
  obtain ⟨hcolB⟩ : Nonempty (IsColimit (BinaryCofan.mk s
      (sectionComplement (pullback.snd p (pullback.snd w f)) s hs).ι)) := by
    refine nonempty_isColimit_binaryCofanMk_of_isCompl s _ ?_
    rw [Scheme.Opens.opensRange_ι]
    exact isCompl_opensRange_sectionComplement (pullback.snd p (pullback.snd w f)) s hs
  have hA : a ≫ (hcolA.coconePointUniqueUpToIso hcolB).hom = s :=
    hcolA.comp_coconePointUniqueUpToIso_hom hcolB ⟨WalkingPair.left⟩
  have hB : b ≫ (hcolA.coconePointUniqueUpToIso hcolB).hom =
      (sectionComplement (pullback.snd p (pullback.snd w f)) s hs).ι :=
    hcolA.comp_coconePointUniqueUpToIso_hom hcolB ⟨WalkingPair.right⟩
  refine ⟨(W ⨿ V' : Scheme.{u}), coprod.desc (𝟙 W) q', etale_coprod _ _ inferInstance hq',
    inferInstance, hcolA.coconePointUniqueUpToIso hcolB, ?_⟩
  refine hcolA.hom_ext ?_
  rintro ⟨(_ | _)⟩
  · show a ≫ _ = a ≫ _
    rw [ha₂, ← Category.assoc]
    exact (congrArg (· ≫ _) hA).trans hs
  · show b ≫ _ = b ≫ _
    rw [hb₂, ← he', Iso.inv_hom_id_assoc, ← Category.assoc]
    exact congrArg (· ≫ _) hB

/-! ### The inductive step, and the affine case -/

/-- **The inductive step of the second proof of Stacks Project, Tag 04DZ.** Granted the descent
statement `Stacks.Etale.EtaleDescentAlongAffineCover`, the affine case for a bound of `n` on the
fibre degrees implies the affine case for a bound of `n + 1`.

Stacks Project, Tag 04DW in the affine form
`Stacks.EtaleCohomology.exists_affine_etale_surjective_pullback` dominates `U` by the base change
of an affine `W` étale over `Y`; `Stacks.Etale.exists_affine_etale_coproduct_pullback_iso` turns
that domination and the inductive hypothesis into an affine scheme `V''` étale over `W` whose
base change to `W_X` is `U ×_X W_X`, and the descent statement descends `V''` to `Y`. The
affineness of the descended scheme is recovered from
`Stacks.Etale.isAffine_of_isAffine_pullback`. -/
theorem essSurjAffineEtalePullbackBounded_succ (hdesc : EtaleDescentAlongAffineCover.{u}) (n : ℕ)
    (ih : EssSurjAffineEtalePullbackBounded.{u} n) :
    EssSurjAffineEtalePullbackBounded.{u} (n + 1) := by
  intro X Y f hf hX hY U p hp hU hdeg
  obtain ⟨_, -, -⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp hf
  -- Tag 04DW with an affine dominating scheme
  obtain ⟨W, w, hw, hWaff, k₀, hk₀surj, hk₀⟩ :=
    EtaleCohomology.exists_affine_etale_surjective_pullback f
      (EtaleCohomology.isHomeomorph_base_of_universalHomeomorphism f).isClosedEmbedding p hp
  -- read the domination over `pullback w f` rather than over `pullback f w`
  obtain ⟨k, hksurj, hk⟩ : ∃ k : (pullback w f : Scheme.{u}) ⟶ U,
      Surjective k ∧ k ≫ p = pullback.snd w f :=
    ⟨(pullbackSymmetry w f).hom ≫ k₀, inferInstance, by
      rw [Category.assoc, hk₀, pullbackSymmetry_hom_comp_fst]⟩
  -- the coproduct `V'' = W ⨿ V'` over `W`
  obtain ⟨V'', v'', hv'', hV''aff, e, he⟩ :=
    exists_affine_etale_coproduct_pullback_iso ih f w hw hWaff p hp hU hdeg k hk
  -- `U` lies over the image of `W_X`, because `k` is surjective
  have himg : Set.range p.base ⊆ Set.range (pullback.snd w f).base := by
    rintro x ⟨u, rfl⟩
    obtain ⟨t, ht⟩ := hksurj.surj u
    refine ⟨t, ?_⟩
    simpa [ht] using (congrArg (fun m : (pullback w f : Scheme.{u}) ⟶ X ↦ m.base t) hk).symm
  -- the descent of `V''` from `W` to `Y`
  obtain ⟨V, q, hq, eU, heU⟩ :=
    hdesc f hf hX hY W w hw hWaff U p hp hU himg V'' v'' hv'' hV''aff e he
  exact ⟨V, q, hq, isAffine_of_isAffine_pullback f q (IsAffine.of_isIso eU.hom), eU, heU⟩

/-- **The affine case of Stacks Project, Tag 04E0 follows from the descent statement alone.**
Granted `Stacks.Etale.EtaleDescentAlongAffineCover`, the hypothesis
`Stacks.Etale.EssSurjAffineEtalePullback` carried by
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineCase` holds, and with
it the essential surjectivity half of Stacks Project, Tags 04DZ and 04E0. -/
theorem essSurjAffineEtalePullback_of_etaleDescentAlongAffineCover
    (hdesc : EtaleDescentAlongAffineCover.{u}) : EssSurjAffineEtalePullback.{u} :=
  essSurjAffineEtalePullback_of_inductiveStep fun n _ ih ↦
    essSurjAffineEtalePullbackBounded_succ hdesc n ih

/-- **Topological invariance of the small étale site from the descent statement.** Granted
`Stacks.Etale.EtaleDescentAlongAffineCover`, base change along an integral, universally injective
and surjective morphism of schemes is an equivalence from the schemes étale over the target to
the schemes étale over the source. -/
theorem etalePullback_isEquivalence_of_etaleDescentAlongAffineCover
    (hdesc : EtaleDescentAlongAffineCover.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    [UniversallyInjective f] [Surjective f] :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show Y.Etale ⥤ X.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ f).IsEquivalence :=
  have : UniversalHomeomorphism f :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).2
      ⟨inferInstance, inferInstance, inferInstance⟩
  etalePullback_isEquivalence_of_forall_exists_pullback_iso f
    (exists_etale_pullback_iso_of_essSurjAffine
      (essSurjAffineEtalePullback_of_etaleDescentAlongAffineCover hdesc) f)

end Stacks.Etale

end

end
