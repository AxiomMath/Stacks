module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceEquivalence

/-!
# Base change of étale schemes along a binary coproduct

Let `f : X ⟶ Y` be a morphism of schemes and let `q₁ : V₁ ⟶ Y` and `q₂ : V₂ ⟶ Y` be schemes over
`Y`. The base change of the coproduct `V₁ ⨿ V₂` along `f` is the coproduct of the two base
changes, because binary coproducts of schemes are van Kampen. Consequently a scheme over `X`
which is a disjoint union of two pieces, each of which is a base change of a scheme étale over
`Y`, is itself the base change of a scheme étale over `Y`.

The last statement is the closure of the essential image of base change on small étale sites
under binary disjoint unions. It is the step with which the second proof of Stacks Project,
Tag 04DZ assembles `W ⨿ V'` out of the two halves produced by its induction, and it is the shape
in which the splitting of Stacks Project, Tag 0BTN —
`Stacks.Etale.exists_coprod_isFinite_and_isEmpty_closedFiber`, whose conclusion is
`IsIso (coprod.desc iFin iAway)` — can be fed back into an essential-surjectivity argument.

## Main definitions

* `Stacks.Etale.coprodBaseChangeInl` and `Stacks.Etale.coprodBaseChangeInr` are the two
  canonical morphisms from the base change of a summand to the base change of the coproduct.
* `Stacks.Etale.coprodBaseChangeIso` identifies the base change of a binary coproduct with a
  scheme presented as a binary coproduct of the two base changes.

## Main results

* `Stacks.Etale.etale_coprodDesc` — a morphism out of a binary coproduct is étale when both of
  its components are.
* `Stacks.Etale.isPullback_coprodBaseChangeInl` and
  `Stacks.Etale.isPullback_coprodBaseChangeInr` — each summand's base change is the base change
  of the corresponding coproduct injection.
* `Stacks.Etale.nonempty_isColimit_binaryCofanMk_coprodBaseChange` — base change along an
  arbitrary morphism of schemes takes a binary coproduct to a binary coproduct.
* `Stacks.Etale.exists_etale_pullback_iso_of_isColimit_binaryCofanMk`,
  `Stacks.Etale.exists_etale_pullback_iso_of_isIso_coprodDesc` and
  `Stacks.Etale.exists_etale_pullback_iso_of_isCompl` — the essential image of base change on
  étale schemes is closed under binary disjoint unions, stated for the three presentations of a
  disjoint union which occur in practice: a colimiting binary cofan, an invertible
  `CategoryTheory.Limits.coprod.desc`, and a pair of complementary open subschemes.

## Implementation notes

The statements about the essential image are written in the elementary existential form used by
`Stacks.Etale.essSurj_etalePullback_of_forall_exists_pullback_iso`, carrying no over-category
data, so that they compose with the rest of the topological-invariance development without
bookkeeping.

The comparison morphisms `Stacks.Etale.coprodBaseChangeDesc` and
`Stacks.Etale.coprodBaseChangeLift` are introduced as named definitions whose declared types are
written at `pullback (coprod.desc q₁ q₂) f` rather than at the cocone point
`(BinaryCofan.mk _ _).pt` of the colimit they are built from. The two spellings are
definitionally equal and not syntactically equal, and the second one makes the goals of the
isomorphism's two triangle identities ill-typed at `implicit` transparency, so no rewrite fires
in them. Stating the comparison maps at the first spelling removes the crossing. The same
crossing is why `Stacks.Etale.isColimitBinaryCofanMkOfIsIsoCoprodDesc` names the isomorphism
`U₁ ⨿ U₂ ≅ U` before handing it to `CategoryTheory.Limits.Cocone.ext`: inlined, the `IsIso`
instance is sought at the unreduced cocone point and is not found, although it is the
declaration's own instance argument.

Neither the distributivity statement nor the closure statement needs `f` to be a universal
homeomorphism; only the étaleness of the descended objects is used.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 0BTN](https://stacks.math.columbia.edu/tag/0BTN)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A morphism out of a binary coproduct of schemes is étale when both of its components are. -/
theorem etale_coprodDesc {V₁ V₂ : Scheme.{u}} (q₁ : V₁ ⟶ Y) (q₂ : V₂ ⟶ Y)
    [Etale q₁] [Etale q₂] : Etale (coprod.desc q₁ q₂) := by
  have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (coprodOpenCover.{u, u} V₁ V₂)]
  rintro (⟨⟩ | ⟨⟩)
  · show Etale (coprod.inl ≫ coprod.desc q₁ q₂)
    rw [coprod.inl_desc]
    infer_instance
  · show Etale (coprod.inr ≫ coprod.desc q₁ q₂)
    rw [coprod.inr_desc]
    infer_instance

variable {V₁ V₂ : Scheme.{u}}

/-- The canonical morphism from the base change of the first summand to the base change of a
binary coproduct. -/
def coprodBaseChangeInl (q₁ : V₁ ⟶ Y) (q₂ : V₂ ⟶ Y) (f : X ⟶ Y) :
    pullback q₁ f ⟶ pullback (coprod.desc q₁ q₂) f :=
  pullback.map q₁ f (coprod.desc q₁ q₂) f coprod.inl (𝟙 X) (𝟙 Y)
    (by rw [Category.comp_id, coprod.inl_desc]) (by simp)

/-- The canonical morphism from the base change of the second summand to the base change of a
binary coproduct. -/
def coprodBaseChangeInr (q₁ : V₁ ⟶ Y) (q₂ : V₂ ⟶ Y) (f : X ⟶ Y) :
    pullback q₂ f ⟶ pullback (coprod.desc q₁ q₂) f :=
  pullback.map q₂ f (coprod.desc q₁ q₂) f coprod.inr (𝟙 X) (𝟙 Y)
    (by rw [Category.comp_id, coprod.inr_desc]) (by simp)

variable (q₁ : V₁ ⟶ Y) (q₂ : V₂ ⟶ Y) (f : X ⟶ Y)

/-- The morphism `coprodBaseChangeInl` commutes with the second projections to `X`. -/
@[reassoc (attr := simp)]
lemma coprodBaseChangeInl_snd :
    coprodBaseChangeInl q₁ q₂ f ≫ pullback.snd (coprod.desc q₁ q₂) f = pullback.snd q₁ f :=
  pullback.lift_snd _ _ _

/-- The morphism `coprodBaseChangeInr` commutes with the second projections to `X`. -/
@[reassoc (attr := simp)]
lemma coprodBaseChangeInr_snd :
    coprodBaseChangeInr q₁ q₂ f ≫ pullback.snd (coprod.desc q₁ q₂) f = pullback.snd q₂ f :=
  pullback.lift_snd _ _ _

/-- The first projection of `coprodBaseChangeInl` is the first projection followed by the first
coproduct injection. -/
@[reassoc (attr := simp)]
lemma coprodBaseChangeInl_fst :
    coprodBaseChangeInl q₁ q₂ f ≫ pullback.fst (coprod.desc q₁ q₂) f =
      pullback.fst q₁ f ≫ coprod.inl :=
  pullback.lift_fst _ _ _

/-- The first projection of `coprodBaseChangeInr` is the first projection followed by the second
coproduct injection. -/
@[reassoc (attr := simp)]
lemma coprodBaseChangeInr_fst :
    coprodBaseChangeInr q₁ q₂ f ≫ pullback.fst (coprod.desc q₁ q₂) f =
      pullback.fst q₂ f ≫ coprod.inr :=
  pullback.lift_fst _ _ _

/-- The base change of the first summand is the base change of the first coproduct injection
along the first projection of `V₁ ⨿ V₂ ×_Y X`. -/
theorem isPullback_coprodBaseChangeInl :
    IsPullback (coprodBaseChangeInl q₁ q₂ f) (pullback.fst q₁ f)
      (pullback.fst (coprod.desc q₁ q₂) f) coprod.inl := by
  refine IsPullback.of_right (h₁₂ := pullback.snd (coprod.desc q₁ q₂) f) ?_ ?_
    (IsPullback.of_hasPullback (coprod.desc q₁ q₂) f).flip
  · rw [coprodBaseChangeInl_snd, coprod.inl_desc]
    exact (IsPullback.of_hasPullback q₁ f).flip
  · simp

/-- The base change of the second summand is the base change of the second coproduct injection
along the first projection of `V₁ ⨿ V₂ ×_Y X`. -/
theorem isPullback_coprodBaseChangeInr :
    IsPullback (coprodBaseChangeInr q₁ q₂ f) (pullback.fst q₂ f)
      (pullback.fst (coprod.desc q₁ q₂) f) coprod.inr := by
  refine IsPullback.of_right (h₁₂ := pullback.snd (coprod.desc q₁ q₂) f) ?_ ?_
    (IsPullback.of_hasPullback (coprod.desc q₁ q₂) f).flip
  · rw [coprodBaseChangeInr_snd, coprod.inr_desc]
    exact (IsPullback.of_hasPullback q₂ f).flip
  · simp

/-- **Base change takes a binary coproduct of schemes to a binary coproduct.** The base change of
`V₁ ⨿ V₂` along any morphism `f : X ⟶ Y` is the coproduct of the base changes of `V₁` and of
`V₂`, with the two canonical morphisms as its injections.

This is the van Kampen property of binary coproducts of schemes, read at the two projections of
the fibre products. -/
theorem nonempty_isColimit_binaryCofanMk_coprodBaseChange :
    Nonempty (IsColimit
      (BinaryCofan.mk (coprodBaseChangeInl q₁ q₂ f) (coprodBaseChangeInr q₁ q₂ f))) := by
  have hvk : IsVanKampenColimit
      (BinaryCofan.mk (coprod.inl : V₁ ⟶ V₁ ⨿ V₂) (coprod.inr : V₂ ⟶ V₁ ⨿ V₂)) :=
    FinitaryExtensive.vanKampen _ (coprodIsCoprod V₁ V₂)
  rw [BinaryCofan.isVanKampen_iff] at hvk
  exact (hvk (BinaryCofan.mk (coprodBaseChangeInl q₁ q₂ f) (coprodBaseChangeInr q₁ q₂ f))
    (pullback.fst q₁ f) (pullback.fst q₂ f) (pullback.fst (coprod.desc q₁ q₂) f)
    (coprodBaseChangeInl_fst q₁ q₂ f).symm
    (coprodBaseChangeInr_fst q₁ q₂ f).symm).mpr
      ⟨isPullback_coprodBaseChangeInl q₁ q₂ f, isPullback_coprodBaseChangeInr q₁ q₂ f⟩

variable {U U₁ U₂ : Scheme.{u}}

/-- The comparison morphism out of the base change of a binary coproduct. Its declared type is
written at `pullback (coprod.desc q₁ q₂) f`, not at the cocone point of the binary cofan it is
built from, so that rewriting in it stays type-correct. -/
def coprodBaseChangeDesc (q₁ : V₁ ⟶ Y) (q₂ : V₂ ⟶ Y) (f : X ⟶ Y)
    (j₁ : U₁ ⟶ U) (j₂ : U₂ ⟶ U)
    (hP : IsColimit
      (BinaryCofan.mk (coprodBaseChangeInl q₁ q₂ f) (coprodBaseChangeInr q₁ q₂ f)))
    (e₁ : pullback q₁ f ≅ U₁) (e₂ : pullback q₂ f ≅ U₂) :
    pullback (coprod.desc q₁ q₂) f ⟶ U :=
  BinaryCofan.IsColimit.desc hP (e₁.hom ≫ j₁) (e₂.hom ≫ j₂)

/-- The comparison morphism into the base change of a binary coproduct. -/
def coprodBaseChangeLift (q₁ : V₁ ⟶ Y) (q₂ : V₂ ⟶ Y) (f : X ⟶ Y)
    {j₁ : U₁ ⟶ U} {j₂ : U₂ ⟶ U} (hU : IsColimit (BinaryCofan.mk j₁ j₂))
    (e₁ : pullback q₁ f ≅ U₁) (e₂ : pullback q₂ f ≅ U₂) :
    U ⟶ pullback (coprod.desc q₁ q₂) f :=
  BinaryCofan.IsColimit.desc hU (e₁.inv ≫ coprodBaseChangeInl q₁ q₂ f)
    (e₂.inv ≫ coprodBaseChangeInr q₁ q₂ f)

variable {j₁ : U₁ ⟶ U} {j₂ : U₂ ⟶ U}
  (hU : IsColimit (BinaryCofan.mk j₁ j₂))
  (hP : IsColimit (BinaryCofan.mk (coprodBaseChangeInl q₁ q₂ f) (coprodBaseChangeInr q₁ q₂ f)))
  (e₁ : pullback q₁ f ≅ U₁) (e₂ : pullback q₂ f ≅ U₂)

/-- The restriction of `coprodBaseChangeDesc` along `coprodBaseChangeInl` is `e₁.hom ≫ j₁`. -/
@[reassoc]
lemma coprodBaseChangeInl_coprodBaseChangeDesc :
    coprodBaseChangeInl q₁ q₂ f ≫ coprodBaseChangeDesc q₁ q₂ f j₁ j₂ hP e₁ e₂ = e₁.hom ≫ j₁ :=
  BinaryCofan.IsColimit.inl_desc hP (e₁.hom ≫ j₁) (e₂.hom ≫ j₂)

/-- The restriction of `coprodBaseChangeDesc` along `coprodBaseChangeInr` is `e₂.hom ≫ j₂`. -/
@[reassoc]
lemma coprodBaseChangeInr_coprodBaseChangeDesc :
    coprodBaseChangeInr q₁ q₂ f ≫ coprodBaseChangeDesc q₁ q₂ f j₁ j₂ hP e₁ e₂ = e₂.hom ≫ j₂ :=
  BinaryCofan.IsColimit.inr_desc hP (e₁.hom ≫ j₁) (e₂.hom ≫ j₂)

/-- The restriction of `coprodBaseChangeLift` along `j₁` is `e₁.inv ≫ coprodBaseChangeInl`. -/
@[reassoc]
lemma inl_coprodBaseChangeLift :
    j₁ ≫ coprodBaseChangeLift q₁ q₂ f hU e₁ e₂ = e₁.inv ≫ coprodBaseChangeInl q₁ q₂ f :=
  BinaryCofan.IsColimit.inl_desc hU (e₁.inv ≫ coprodBaseChangeInl q₁ q₂ f)
    (e₂.inv ≫ coprodBaseChangeInr q₁ q₂ f)

/-- The restriction of `coprodBaseChangeLift` along `j₂` is `e₂.inv ≫ coprodBaseChangeInr`. -/
@[reassoc]
lemma inr_coprodBaseChangeLift :
    j₂ ≫ coprodBaseChangeLift q₁ q₂ f hU e₁ e₂ = e₂.inv ≫ coprodBaseChangeInr q₁ q₂ f :=
  BinaryCofan.IsColimit.inr_desc hU (e₁.inv ≫ coprodBaseChangeInl q₁ q₂ f)
    (e₂.inv ≫ coprodBaseChangeInr q₁ q₂ f)

/-- The composite `coprodBaseChangeDesc ≫ coprodBaseChangeLift` is the identity. -/
lemma coprodBaseChangeDesc_coprodBaseChangeLift :
    coprodBaseChangeDesc q₁ q₂ f j₁ j₂ hP e₁ e₂ ≫ coprodBaseChangeLift q₁ q₂ f hU e₁ e₂ =
      𝟙 (pullback (coprod.desc q₁ q₂) f) := by
  have hA : coprodBaseChangeInl q₁ q₂ f ≫
      (coprodBaseChangeDesc q₁ q₂ f j₁ j₂ hP e₁ e₂ ≫ coprodBaseChangeLift q₁ q₂ f hU e₁ e₂) =
        coprodBaseChangeInl q₁ q₂ f ≫ 𝟙 (pullback (coprod.desc q₁ q₂) f) := by
    rw [coprodBaseChangeInl_coprodBaseChangeDesc_assoc, inl_coprodBaseChangeLift,
      ← Category.assoc, e₁.hom_inv_id, Category.id_comp, Category.comp_id]
  have hB : coprodBaseChangeInr q₁ q₂ f ≫
      (coprodBaseChangeDesc q₁ q₂ f j₁ j₂ hP e₁ e₂ ≫ coprodBaseChangeLift q₁ q₂ f hU e₁ e₂) =
        coprodBaseChangeInr q₁ q₂ f ≫ 𝟙 (pullback (coprod.desc q₁ q₂) f) := by
    rw [coprodBaseChangeInr_coprodBaseChangeDesc_assoc, inr_coprodBaseChangeLift,
      ← Category.assoc, e₂.hom_inv_id, Category.id_comp, Category.comp_id]
  exact BinaryCofan.IsColimit.hom_ext hP hA hB

/-- The composite `coprodBaseChangeLift ≫ coprodBaseChangeDesc` is the identity. -/
lemma coprodBaseChangeLift_coprodBaseChangeDesc :
    coprodBaseChangeLift q₁ q₂ f hU e₁ e₂ ≫ coprodBaseChangeDesc q₁ q₂ f j₁ j₂ hP e₁ e₂ =
      𝟙 U := by
  have hA : j₁ ≫ (coprodBaseChangeLift q₁ q₂ f hU e₁ e₂ ≫
      coprodBaseChangeDesc q₁ q₂ f j₁ j₂ hP e₁ e₂) = j₁ ≫ 𝟙 U := by
    rw [inl_coprodBaseChangeLift_assoc, coprodBaseChangeInl_coprodBaseChangeDesc,
      ← Category.assoc, e₁.inv_hom_id, Category.id_comp, Category.comp_id]
  have hB : j₂ ≫ (coprodBaseChangeLift q₁ q₂ f hU e₁ e₂ ≫
      coprodBaseChangeDesc q₁ q₂ f j₁ j₂ hP e₁ e₂) = j₂ ≫ 𝟙 U := by
    rw [inr_coprodBaseChangeLift_assoc, coprodBaseChangeInr_coprodBaseChangeDesc,
      ← Category.assoc, e₂.inv_hom_id, Category.id_comp, Category.comp_id]
  exact BinaryCofan.IsColimit.hom_ext hU hA hB

/-- The base change of a binary coproduct of schemes over `Y`, identified with a scheme over `X`
presented as a binary coproduct of the two base changes. -/
@[simps]
def coprodBaseChangeIso : pullback (coprod.desc q₁ q₂) f ≅ U where
  hom := coprodBaseChangeDesc q₁ q₂ f j₁ j₂ hP e₁ e₂
  inv := coprodBaseChangeLift q₁ q₂ f hU e₁ e₂
  hom_inv_id := coprodBaseChangeDesc_coprodBaseChangeLift q₁ q₂ f hU hP e₁ e₂
  inv_hom_id := coprodBaseChangeLift_coprodBaseChangeDesc q₁ q₂ f hU hP e₁ e₂

/-- **The essential image of base change on étale schemes is closed under binary disjoint
unions.** Let `U` be a scheme over `X` which is the coproduct of `U₁` and `U₂`. If each of `U₁`
and `U₂` is, over `X`, the base change along `f` of a scheme étale over `Y`, then so is `U`.

The hypotheses and the conclusion are in the elementary form consumed by
`Stacks.Etale.essSurj_etalePullback_of_forall_exists_pullback_iso`. -/
theorem exists_etale_pullback_iso_of_isColimit_binaryCofanMk (f : X ⟶ Y)
    (p : U ⟶ X) (j₁ : U₁ ⟶ U) (j₂ : U₂ ⟶ U)
    (hU : IsColimit (BinaryCofan.mk j₁ j₂))
    (h₁ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U₁),
      e.hom ≫ (j₁ ≫ p) = pullback.snd q f)
    (h₂ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U₂),
      e.hom ≫ (j₂ ≫ p) = pullback.snd q f) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f := by
  obtain ⟨W₁, r₁, hr₁, d₁, hd₁⟩ := h₁
  obtain ⟨W₂, r₂, hr₂, d₂, hd₂⟩ := h₂
  have : Etale r₁ := hr₁
  have : Etale r₂ := hr₂
  obtain ⟨hP⟩ := nonempty_isColimit_binaryCofanMk_coprodBaseChange r₁ r₂ f
  refine ⟨W₁ ⨿ W₂, coprod.desc r₁ r₂, etale_coprodDesc r₁ r₂,
    coprodBaseChangeIso r₁ r₂ f hU hP d₁ d₂, ?_⟩
  have hA : coprodBaseChangeInl r₁ r₂ f ≫
      ((coprodBaseChangeIso r₁ r₂ f hU hP d₁ d₂).hom ≫ p) =
        coprodBaseChangeInl r₁ r₂ f ≫ pullback.snd (coprod.desc r₁ r₂) f := by
    rw [coprodBaseChangeIso_hom, coprodBaseChangeInl_coprodBaseChangeDesc_assoc, hd₁,
      coprodBaseChangeInl_snd]
  have hB : coprodBaseChangeInr r₁ r₂ f ≫
      ((coprodBaseChangeIso r₁ r₂ f hU hP d₁ d₂).hom ≫ p) =
        coprodBaseChangeInr r₁ r₂ f ≫ pullback.snd (coprod.desc r₁ r₂) f := by
    rw [coprodBaseChangeIso_hom, coprodBaseChangeInr_coprodBaseChangeDesc_assoc, hd₂,
      coprodBaseChangeInr_snd]
  exact BinaryCofan.IsColimit.hom_ext hP hA hB

/-- A scheme presented as a disjoint union by an invertible
`CategoryTheory.Limits.coprod.desc` is a binary coproduct. This is the presentation in which the
splitting of Stacks Project, Tag 0BTN is stated. -/
def isColimitBinaryCofanMkOfIsIsoCoprodDesc (j₁ : U₁ ⟶ U) (j₂ : U₂ ⟶ U)
    [IsIso (coprod.desc j₁ j₂)] : IsColimit (BinaryCofan.mk j₁ j₂) :=
  let e : (U₁ ⨿ U₂) ≅ U := asIso (coprod.desc j₁ j₂)
  IsColimit.ofIsoColimit (coprodIsCoprod U₁ U₂)
    (Cocone.ext e (by
      rintro (⟨⟩ | ⟨⟩)
      · exact coprod.inl_desc j₁ j₂
      · exact coprod.inr_desc j₁ j₂))

/-- **The essential image of base change on étale schemes is closed under binary disjoint
unions**, for a disjoint union presented by an invertible
`CategoryTheory.Limits.coprod.desc`. -/
theorem exists_etale_pullback_iso_of_isIso_coprodDesc (f : X ⟶ Y)
    (p : U ⟶ X) (j₁ : U₁ ⟶ U) (j₂ : U₂ ⟶ U) [IsIso (coprod.desc j₁ j₂)]
    (h₁ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U₁),
      e.hom ≫ (j₁ ≫ p) = pullback.snd q f)
    (h₂ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U₂),
      e.hom ≫ (j₂ ≫ p) = pullback.snd q f) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f :=
  exists_etale_pullback_iso_of_isColimit_binaryCofanMk f p j₁ j₂
    (isColimitBinaryCofanMkOfIsIsoCoprodDesc j₁ j₂) h₁ h₂

/-- **The essential image of base change on étale schemes is closed under passage to a pair of
complementary open subschemes.** If `U₁` and `U₂` are complementary open subschemes of a scheme
`U` over `X` and each is the base change along `f` of a scheme étale over `Y`, then so is `U`. -/
theorem exists_etale_pullback_iso_of_isCompl (f : X ⟶ Y)
    (p : U ⟶ X) (j₁ : U₁ ⟶ U) (j₂ : U₂ ⟶ U) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hj : IsCompl j₁.opensRange j₂.opensRange)
    (h₁ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U₁),
      e.hom ≫ (j₁ ≫ p) = pullback.snd q f)
    (h₂ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U₂),
      e.hom ≫ (j₂ ≫ p) = pullback.snd q f) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f :=
  exists_etale_pullback_iso_of_isColimit_binaryCofanMk f p j₁ j₂
    (nonempty_isColimit_binaryCofanMk_of_isCompl j₁ j₂ hj).some h₁ h₂

end Stacks.Etale

end

end
