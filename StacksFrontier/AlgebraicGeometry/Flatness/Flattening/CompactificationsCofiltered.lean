module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense

/-!
# Compactifications form a cofiltered category

Let `X` be a scheme over a quasi-compact and quasi-separated base `S`, admitting a
quasi-compact compactification. Then the category of compactifications of `X` over `S` is
cofiltered, and the full subcategory of those compactifications in which `X` has dense and
scheme-theoretically dense image is initial in it.

## Main definitions

* `AlgebraicGeometry.CategoryOfCompactifications.IsDenseCompactification` is the property
  that the image of the open immersion of a compactification is both topologically dense and
  scheme-theoretically dense.

## Main results

* `AlgebraicGeometry.CategoryOfCompactifications.isCofiltered` states that the category of
  compactifications is cofiltered.
* `AlgebraicGeometry.CategoryOfCompactifications.denseCompactification_initial` states that
  the inclusion of the dense compactifications is initial.

## Implementation notes

Two compactifications are dominated by the scheme-theoretic image of `X` inside the product
of the two ambient schemes over `S`; two parallel morphisms of compactifications are
equalized by the scheme-theoretic image of `X` inside their equalizer, which is a closed
subscheme of the source ambient scheme because the target is separated over `S`. In both
cases the open immersion of `X` into the scheme-theoretic image is supplied by
`AlgebraicGeometry.isOpenImmersion_toImage`, whose quasi-compactness hypothesis holds because
the assumed quasi-compact compactification forces `X` to be a compact space.

The auxiliary morphisms are introduced by `obtain` from an existence statement recording only
the identities their construction supplies, so that typeclass inference sees them as opaque
local constants rather than unfolding the pullbacks and equalizers behind them.

Initiality is `CategoryTheory.Functor.Initial`, the notion registered for Stacks Project Tag
09WP; being cofiltered is `CategoryTheory.IsCofiltered`, registered for Tag 04AZ.

## References

* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace CategoryOfCompactifications

variable (D : CategoryOfCompactifications.{u})

/-- The ambient scheme of a compactification is a compact space, being proper over a
quasi-compact base. -/
lemma compactSpace_space (j : D.category) : CompactSpace j.space :=
  QuasiCompact.compactSpace_of_compactSpace j.toBase

/-- The ambient scheme of a compactification is a quasi-separated space, being separated over
a quasi-separated base. -/
lemma quasiSeparatedSpace_space (j : D.category) : QuasiSeparatedSpace j.space :=
  quasiSeparatedSpace_of_quasiSeparated j.toBase

/-- The scheme being compactified is a compact space: it is quasi-compact over the ambient
scheme of the assumed quasi-compact compactification, which is itself compact. -/
lemma compactSpace_X : CompactSpace D.X.left := by
  obtain ⟨j, hj⟩ := D.exists_quasiCompact_compactification
  let : QuasiCompact j.immersion := hj
  let : CompactSpace j.space := compactSpace_space D j
  exact QuasiCompact.compactSpace_of_compactSpace j.immersion

variable {D} in
/-- The compactification of `X` given by the scheme-theoretic image of an immersion `i` of `X`
into a quasi-separated scheme proper over the base. -/
private noncomputable def ofImmersion {Y : Scheme.{u}} (i : D.X.left ⟶ Y) (p : Y ⟶ D.S)
    [IsImmersion i] [IsProper p] [QuasiSeparatedSpace Y] (hi : i ≫ p = D.X.hom) : D.category :=
  let : CompactSpace D.X.left := compactSpace_X D
  let : IsOpenImmersion i.toImage := isOpenImmersion_toImage i (Or.inl inferInstance)
  ⟨StructuredArrow.mk (Y := Over.mk (i.imageι ≫ p))
      (Over.homMk i.toImage (by
        change i.toImage ≫ i.imageι ≫ p = D.X.hom
        rw [← Category.assoc, Scheme.Hom.toImage_imageι, hi])),
    ⟨by exact (inferInstance : IsOpenImmersion i.toImage),
      by exact (inferInstance : IsProper (i.imageι ≫ p))⟩⟩

variable {D} in
/-- The morphism from `ofImmersion i p hi` to a compactification `j` induced by a morphism
`q` of ambient schemes over the base extending the immersion of `j`. -/
private noncomputable def ofImmersionHom {Y : Scheme.{u}} {i : D.X.left ⟶ Y} {p : Y ⟶ D.S}
    [IsImmersion i] [IsProper p] [QuasiSeparatedSpace Y] (hi : i ≫ p = D.X.hom) {j : D.category}
    (q : Y ⟶ j.space) (hq : q ≫ j.toBase = p) (hiq : i ≫ q = j.immersion) :
    ofImmersion i p hi ⟶ j :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk (i.imageι ≫ q) (by
      change (i.imageι ≫ q) ≫ j.toBase = i.imageι ≫ p
      rw [Category.assoc, hq])) (by
      apply CostructuredArrow.hom_ext
      change i.toImage ≫ i.imageι ≫ q = j.immersion
      rw [← Category.assoc, Scheme.Hom.toImage_imageι, hiq]))

/-- Any two compactifications are dominated by a third, namely the scheme-theoretic image of
the map of `X` into the product of the two ambient schemes over the base. -/
private lemma exists_cone_objs (j₁ j₂ : D.category) :
    ∃ (k : D.category) (_ : k ⟶ j₁) (_ : k ⟶ j₂), True := by
  let : QuasiSeparatedSpace j₁.space := quasiSeparatedSpace_space D j₁
  have hbase₁ : j₁.immersion ≫ j₁.toBase = D.X.hom := Over.w j₁.obj.hom
  obtain ⟨P, q₁, q₂, hq₁, hq, m, hm₁, hm₂⟩ :
      ∃ (P : Scheme.{u}) (q₁ : P ⟶ j₁.space) (q₂ : P ⟶ j₂.space), IsProper q₁ ∧
        q₁ ≫ j₁.toBase = q₂ ≫ j₂.toBase ∧ ∃ m : D.X.left ⟶ P,
          m ≫ q₁ = j₁.immersion ∧ m ≫ q₂ = j₂.immersion :=
    ⟨pullback j₁.toBase j₂.toBase, pullback.fst _ _, pullback.snd _ _, inferInstance,
      pullback.condition, pullback.lift j₁.immersion j₂.immersion
        (hbase₁.trans (Over.w j₂.obj.hom).symm),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  let : IsProper q₁ := hq₁
  let : QuasiSeparatedSpace P := quasiSeparatedSpace_of_quasiSeparated q₁
  let : IsImmersion (m ≫ q₁) := by rw [hm₁]; infer_instance
  let : IsImmersion m := IsImmersion.of_comp m q₁
  have hmS : m ≫ q₁ ≫ j₁.toBase = D.X.hom := by rw [← Category.assoc, hm₁, hbase₁]
  exact ⟨ofImmersion m _ hmS, ofImmersionHom hmS q₁ rfl hm₁,
    ofImmersionHom hmS q₂ hq.symm hm₂, trivial⟩

/-- Any two parallel morphisms of compactifications are equalized by a third
compactification, namely the scheme-theoretic image of `X` inside their equalizer. -/
private lemma exists_cone_maps {j₁ j₂ : D.category} (f g : j₁ ⟶ j₂) :
    ∃ (k : D.category) (h : k ⟶ j₁), h ≫ f = h ≫ g := by
  let : QuasiSeparatedSpace j₁.space := quasiSeparatedSpace_space D j₁
  let : IsSeparated j₂.obj.right.hom := (j₂.property.2).toIsSeparated
  have hw : j₁.obj.hom ≫ f.hom.right = j₁.obj.hom ≫ g.hom.right := by
    simpa using (StructuredArrow.w f.hom).trans (StructuredArrow.w g.hom).symm
  obtain ⟨E, c, hcc, hcond, l, hl⟩ :
      ∃ (E : Over D.S) (c : E ⟶ j₁.obj.right), IsClosedImmersion c.left ∧
        c ≫ f.hom.right = c ≫ g.hom.right ∧ ∃ l : D.X ⟶ E, l ≫ c = j₁.obj.hom :=
    ⟨equalizer _ _, equalizer.ι _ _, isClosedImmersion_equalizer_ι_left _ _,
      equalizer.condition _ _, equalizer.lift j₁.obj.hom hw, equalizer.lift_ι _ _⟩
  let : IsClosedImmersion c.left := hcc
  let : QuasiSeparatedSpace E.left := quasiSeparatedSpace_of_quasiSeparated c.left
  have hleft : l.left ≫ c.left = j₁.immersion := by
    simpa [Over.comp_left] using congrArg Over.Hom.left hl
  let : IsImmersion (l.left ≫ c.left) := by rw [hleft]; infer_instance
  let : IsImmersion l.left := IsImmersion.of_comp l.left c.left
  have hlS : l.left ≫ c.left ≫ j₁.toBase = D.X.hom := by
    rw [← Category.assoc, hleft]
    exact Over.w j₁.obj.hom
  refine ⟨ofImmersion l.left _ hlS, ofImmersionHom hlS c.left rfl hleft, ?_⟩
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  apply Over.OverMorphism.ext
  change (l.left.imageι ≫ c.left) ≫ f.hom.right.left =
    (l.left.imageι ≫ c.left) ≫ g.hom.right.left
  have hcl : c.left ≫ f.hom.right.left = c.left ≫ g.hom.right.left := by
    simpa [Over.comp_left] using congrArg Over.Hom.left hcond
  rw [Category.assoc, Category.assoc, hcl]

/-- **Stacks Project, Tag 0ATU.** The category of compactifications of a scheme over a
quasi-compact and quasi-separated base is cofiltered. -/
@[stacks 0ATU "cofiltered"]
instance isCofiltered : IsCofiltered D.category where
  cone_objs := exists_cone_objs D
  cone_maps := @fun _ _ f g ↦ exists_cone_maps D f g
  nonempty := inferInstance

/-- A compactification is dense if the image of its open immersion is both topologically
dense and scheme-theoretically dense in its ambient scheme. -/
abbrev IsDenseCompactification (j : D.category) : Prop :=
  DenseRange j.immersion.base ∧
    Scheme.Opens.IsSchemeTheoreticallyDense j.immersion.opensRange

/-- Every compactification receives a morphism from a dense one, namely the
scheme-theoretic image of `X` in it. -/
private lemma exists_denseCompactification_to (j : D.category) :
    ∃ k : ObjectProperty.FullSubcategory (IsDenseCompactification D : ObjectProperty D.category),
      Nonempty (k.obj ⟶ j) := by
  let : CompactSpace D.X.left := compactSpace_X D
  let : QuasiSeparatedSpace j.space := quasiSeparatedSpace_space D j
  have hiS : j.immersion ≫ j.toBase = D.X.hom := Over.w j.obj.hom
  exact ⟨⟨ofImmersion j.immersion j.toBase hiS,
    (isDominant_toImage j.immersion (Or.inl inferInstance)).denseRange,
    isSchemeTheoreticallyDense_toImage j.immersion (Or.inl inferInstance)⟩,
    ⟨ofImmersionHom hiS (𝟙 _) (Category.id_comp _) (Category.comp_id _)⟩⟩

/-- **Stacks Project, Tag 0ATU.** The compactifications in which the image of `X` is dense and
scheme-theoretically dense form an initial full subcategory of the category of all
compactifications. -/
@[stacks 0ATU "dense_compactifications_initial"]
instance denseCompactification_initial :
    (ObjectProperty.ι (IsDenseCompactification D : ObjectProperty D.category)).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _
    (exists_denseCompactification_to D)

end CategoryOfCompactifications

end AlgebraicGeometry

end
