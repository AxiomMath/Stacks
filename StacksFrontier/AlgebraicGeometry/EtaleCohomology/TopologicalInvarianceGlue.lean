module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceEquivalence
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.CutOut
public import StacksFrontier.AlgebraicGeometry.LimitApproxFunctor.Glue
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.GluePair

/-!
# Base change of étale schemes along a glueing of two schemes

Let `f : X ⟶ Y` be a morphism of schemes. A scheme over `X` which is covered by two open
subschemes, each of which is a base change along `f` of a scheme étale over `Y`, is itself the
base change of a scheme étale over `Y`, provided `f` is a universal homeomorphism. This is the
closure of the essential image of base change on small étale sites under glueing along an open
subscheme, and it is the step with which an essential-surjectivity argument for Stacks Project,
Tag 04DZ is run locally on the scheme to be descended rather than globally.

The descent is built by glueing the two schemes over `Y` along the open subscheme which cuts out
the overlap. That open subscheme is read off either piece — by
`Stacks.Etale.exists_opens_preimage_eq_of_universalHomeomorphism`, a universal homeomorphism
matches up the open subschemes of its source and target — and the two readings are identified by
the rigidity `Stacks.Etale.exists_iso_of_pullback_iso`. So the transition isomorphism is forced,
and no cocycle condition has to be checked.

The glueing of a pair of schemes along a common open subscheme is
`AlgebraicGeometry.Scheme.gluePair`, a locally directed colimit of a wide span. It therefore
carries no cocycle obligations at all, unlike `AlgebraicGeometry.Scheme.GlueData`, and the
descent morphism out of it is `AlgebraicGeometry.Scheme.gluePairDesc`, with no compatibility
beyond the single equation on the common open subscheme.

## Main definitions

* `AlgebraicGeometry.Scheme.gluePairOpens` is a scheme presented as the glueing of two of its
  open subschemes along their intersection, and
  `AlgebraicGeometry.Scheme.gluePairOpensDesc` is the canonical morphism from it.
* `AlgebraicGeometry.Scheme.gluePairCongr` upgrades the functoriality
  `AlgebraicGeometry.Scheme.gluePairMap` of the glueing in its defining span to an isomorphism
  of glueings.
* `AlgebraicGeometry.Scheme.isoOfOpensCover` identifies two schemes each covered by two open
  subschemes, given compatible identifications of the pieces and of the overlap.
* `Stacks.Etale.baseChangeOver` is the morphism of base changes induced by a morphism over the
  base.

## Main results

* `AlgebraicGeometry.Scheme.gluePairOpensDescIso` — **a scheme is the glueing of two open
  subschemes covering it**, as the canonical morphism out of
  `AlgebraicGeometry.Scheme.gluePairOpens`. This is what turns a pair of covering opens into a
  presentation with free descent.
* `Stacks.Etale.etale_gluePairDesc` — a morphism out of a glueing is étale when both of its
  components are.
* `Stacks.Etale.exists_opens_overlap_iso` — an open subscheme of a base change along a universal
  homeomorphism is itself the base change of an open subscheme of the base.
* `Stacks.Etale.exists_etale_pullback_iso_of_sup_opens`,
  `Stacks.Etale.exists_etale_pullback_iso_of_sup_opensRange` and
  `Stacks.Etale.exists_etale_pullback_iso_of_gluePair` — **the essential image of base change on
  étale schemes is closed under glueing along an open subscheme**, stated for the three
  presentations of such a glueing which occur in practice: two open subschemes covering the
  scheme, two open immersions whose images cover, and `AlgebraicGeometry.Scheme.gluePair` itself.

## Implementation notes

The statements about the essential image are written in the elementary existential form used by
`Stacks.Etale.essSurj_etalePullback_of_forall_exists_pullback_iso`, carrying no over-category
data, so that they compose with the rest of the topological-invariance development, and with the
binary-disjoint-union closure of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCoproduct`, without
bookkeeping.

No hypothesis is made on the overlap: it is descended, not assumed to be descended. Dropping it
is a strengthening, not a weakening.

`AlgebraicGeometry.Scheme.isIso_gluePairOpensDesc` is proved by the locality of isomorphisms at
the target over the two covering opens. Open immersions are *not* local at the source — two
copies of a scheme mapping identically restrict to isomorphisms on each — so the descent morphism
cannot be shown to be an open immersion piecewise; what is local is the statement over each open
of the target, and there the morphism is identified with the inverse of
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` by cancelling the monomorphism `U.ι`.

Two rewrites in this file are done in term mode rather than with `rw`.
`AlgebraicGeometry.Scheme.Hom.opensRange` takes the open-immersion instance as an argument, so
rewriting a morphism underneath it produces an ill-typed motive; and the points of
`U.toScheme` are reached through `(·).1` rather than through a type ascription, because the
carrier of `U.toScheme` and the subtype `↥U` are definitionally but not syntactically equal and
`rw` builds its motive at `implicit` transparency.

## References

* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 01JC](https://stacks.math.columbia.edu/tag/01JC)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {W X Y : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]

/-- The colimit leg of `AlgebraicGeometry.Scheme.gluePair` at the common open subscheme is `f`
followed by the first leg. -/
lemma gluePair_ι_none : colimit.ι (gluePairDiagram f g) none = f ≫ gluePairInl f g :=
  (colimit.w (gluePairDiagram f g) (WidePushoutShape.Hom.init WalkingPair.left)).symm

/-- An open immersion cutting out an open subscheme has the same range as its inclusion. -/
private theorem range_base_eq_of_opensRange_eq {M N : Scheme.{u}} (c : M ⟶ N) [IsOpenImmersion c]
    {P : N.Opens} (h : c.opensRange = P) : Set.range c.base = Set.range P.ι.base := by
  rw [← Scheme.Hom.coe_opensRange, h, Scheme.Opens.range_ι]

/-- A morphism whose restriction over an open subscheme of the target is, up to isomorphism, an
open immersion cutting out exactly the preimage of that open subscheme, restricts to an
isomorphism over it. -/
lemma isIso_morphismRestrict_of_opensRange {G T : Scheme.{u}} (θ : G ⟶ T) (P : T.Opens)
    {A : Scheme.{u}} (j : A ⟶ G) [IsOpenImmersion j] (c : A ≅ P.toScheme)
    (hj : θ ⁻¹ᵁ P = j.opensRange) (hjθ : j ≫ θ = c.hom ≫ P.ι) : IsIso (θ ∣_ P) := by
  have hr := range_base_eq_of_opensRange_eq j hj.symm
  have hα := IsOpenImmersion.isoOfRangeEq_hom_fac j (θ ⁻¹ᵁ P).ι hr
  have h : θ ∣_ P = (IsOpenImmersion.isoOfRangeEq j (θ ⁻¹ᵁ P).ι hr).inv ≫ c.hom := by
    rw [Iso.eq_inv_comp, ← cancel_mono P.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, hα, hjθ]
  rw [h]
  infer_instance

section Opens

variable {T : Scheme.{u}} (A B : T.Opens)

/-- Two open subschemes of a scheme, glued along their intersection. -/
abbrev gluePairOpens : Scheme.{u} :=
  gluePair (T.homOfLE (inf_le_left : A ⊓ B ≤ A)) (T.homOfLE (inf_le_right : A ⊓ B ≤ B))

/-- The leg of `AlgebraicGeometry.Scheme.gluePairOpens` coming from the first open subscheme. -/
abbrev gluePairOpensInl : A.toScheme ⟶ gluePairOpens A B :=
  gluePairInl (T.homOfLE (inf_le_left : A ⊓ B ≤ A)) (T.homOfLE (inf_le_right : A ⊓ B ≤ B))

/-- The leg of `AlgebraicGeometry.Scheme.gluePairOpens` coming from the second open subscheme. -/
abbrev gluePairOpensInr : B.toScheme ⟶ gluePairOpens A B :=
  gluePairInr (T.homOfLE (inf_le_left : A ⊓ B ≤ A)) (T.homOfLE (inf_le_right : A ⊓ B ≤ B))

/-- The canonical morphism from the glueing of two open subschemes to the ambient scheme. -/
def gluePairOpensDesc : gluePairOpens A B ⟶ T :=
  gluePairDesc (T.homOfLE (inf_le_left : A ⊓ B ≤ A)) (T.homOfLE (inf_le_right : A ⊓ B ≤ B))
    A.ι B.ι (by rw [T.homOfLE_ι, T.homOfLE_ι])

/-- The canonical morphism restricts to the inclusion of the first open subscheme. -/
@[reassoc (attr := simp)]
lemma gluePairOpensInl_desc : gluePairOpensInl A B ≫ gluePairOpensDesc A B = A.ι :=
  gluePairInl_desc _ _ _ _ _

/-- The canonical morphism restricts to the inclusion of the second open subscheme. -/
@[reassoc (attr := simp)]
lemma gluePairOpensInr_desc : gluePairOpensInr A B ≫ gluePairOpensDesc A B = B.ι :=
  gluePairInr_desc _ _ _ _ _

/-- The canonical morphism sends a point of the first open subscheme to itself. -/
lemma gluePairOpensDesc_inl_apply (x : A.toScheme) :
    gluePairOpensDesc A B (gluePairOpensInl A B x) = A.ι x := by
  rw [← Scheme.Hom.comp_apply, gluePairOpensInl_desc]

/-- The canonical morphism sends a point of the second open subscheme to itself. -/
lemma gluePairOpensDesc_inr_apply (y : B.toScheme) :
    gluePairOpensDesc A B (gluePairOpensInr A B y) = B.ι y := by
  rw [← Scheme.Hom.comp_apply, gluePairOpensInr_desc]

/-- A point of an open subscheme lying in a smaller open subset comes from that smaller open
subscheme. -/
private theorem exists_homOfLE_apply_eq {A C : T.Opens} (h : C ≤ A) (x : A.toScheme)
    (hx : A.ι x ∈ (C : Set ↥T)) : ∃ w : C.toScheme, T.homOfLE h w = x := by
  obtain ⟨w, hw⟩ := C.range_ι.symm.subset hx
  exact ⟨w, A.ι.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, T.homOfLE_ι, hw])⟩

/-- The preimage of `A` under the canonical morphism is the image of the first leg. -/
lemma preimage_gluePairOpensDesc_left :
    gluePairOpensDesc A B ⁻¹ᵁ A = (gluePairOpensInl A B).opensRange := by
  refine TopologicalSpace.Opens.ext (subset_antisymm ?_ ?_)
  · rintro u hu
    obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := gluePair_jointly_surjective _ _ u
    · exact ⟨x, rfl⟩
    · have hu' : gluePairOpensDesc A B (gluePairOpensInr A B y) ∈ (A : Set ↥T) := hu
      rw [gluePairOpensDesc_inr_apply] at hu'
      obtain ⟨w, hy⟩ := exists_homOfLE_apply_eq (inf_le_right : A ⊓ B ≤ B) y
        (show B.ι y ∈ ((A ⊓ B : T.Opens) : Set ↥T) from ⟨hu', B.range_ι.subset ⟨y, rfl⟩⟩)
      exact ⟨T.homOfLE (inf_le_left : A ⊓ B ≤ A) w, by
        rw [← Scheme.Hom.comp_apply, gluePair_condition, Scheme.Hom.comp_apply, hy]⟩
  · rintro u ⟨x, rfl⟩
    show gluePairOpensDesc A B (gluePairOpensInl A B x) ∈ (A : Set ↥T)
    rw [gluePairOpensDesc_inl_apply]
    exact A.range_ι.subset ⟨x, rfl⟩

/-- The preimage of `B` under the canonical morphism is the image of the second leg. -/
lemma preimage_gluePairOpensDesc_right :
    gluePairOpensDesc A B ⁻¹ᵁ B = (gluePairOpensInr A B).opensRange := by
  refine TopologicalSpace.Opens.ext (subset_antisymm ?_ ?_)
  · rintro u hu
    obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := gluePair_jointly_surjective _ _ u
    · have hu' : gluePairOpensDesc A B (gluePairOpensInl A B x) ∈ (B : Set ↥T) := hu
      rw [gluePairOpensDesc_inl_apply] at hu'
      obtain ⟨w, hx⟩ := exists_homOfLE_apply_eq (inf_le_left : A ⊓ B ≤ A) x
        (show A.ι x ∈ ((A ⊓ B : T.Opens) : Set ↥T) from ⟨A.range_ι.subset ⟨x, rfl⟩, hu'⟩)
      exact ⟨T.homOfLE (inf_le_right : A ⊓ B ≤ B) w, by
        rw [← Scheme.Hom.comp_apply, ← gluePair_condition, Scheme.Hom.comp_apply, hx]⟩
    · exact ⟨y, rfl⟩
  · rintro u ⟨y, rfl⟩
    show gluePairOpensDesc A B (gluePairOpensInr A B y) ∈ (B : Set ↥T)
    rw [gluePairOpensDesc_inr_apply]
    exact B.range_ι.subset ⟨y, rfl⟩

/-- **A scheme is glued from two open subschemes covering it.** -/
lemma isIso_gluePairOpensDesc (hAB : A ⊔ B = ⊤) : IsIso (gluePairOpensDesc A B) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme.{u})
    (fun b : Bool ↦ bif b then A else B) (by rw [iSup_bool_eq]; exact hAB) fun b ↦ ?_
  rw [MorphismProperty.isomorphisms.iff]
  cases b
  · exact isIso_morphismRestrict_of_opensRange _ B (gluePairOpensInr A B) (Iso.refl _)
      (preimage_gluePairOpensDesc_right A B) (by rw [gluePairOpensInr_desc, Iso.refl_hom,
        Category.id_comp])
  · exact isIso_morphismRestrict_of_opensRange _ A (gluePairOpensInl A B) (Iso.refl _)
      (preimage_gluePairOpensDesc_left A B) (by rw [gluePairOpensInl_desc, Iso.refl_hom,
        Category.id_comp])

/-- **A scheme is glued from two open subschemes covering it**, as an isomorphism. -/
def gluePairOpensDescIso (hAB : A ⊔ B = ⊤) : gluePairOpens A B ≅ T :=
  letI := isIso_gluePairOpensDesc A B hAB
  asIso (gluePairOpensDesc A B)

/-- The forward map of `AlgebraicGeometry.Scheme.gluePairOpensDescIso` is the canonical
morphism. -/
@[simp]
lemma gluePairOpensDescIso_hom (hAB : A ⊔ B = ⊤) :
    (gluePairOpensDescIso A B hAB).hom = gluePairOpensDesc A B := rfl

end Opens

section Congr

variable {W' X' Y' : Scheme.{u}} (f' : W' ⟶ X') (g' : W' ⟶ Y')
  [IsOpenImmersion f'] [IsOpenImmersion g']

/-- An isomorphism of glueing data induces an isomorphism of the glueings.  Since the glueing is
a locally directed colimit of a wide span, no cocycle condition enters. -/
def gluePairCongr (eW : W ≅ W') (eX : X ≅ X') (eY : Y ≅ Y')
    (hf : f ≫ eX.hom = eW.hom ≫ f') (hg : g ≫ eY.hom = eW.hom ≫ g') :
    gluePair f g ≅ gluePair f' g' where
  hom := gluePairMap eW.hom eX.hom eY.hom hf hg
  inv := gluePairMap eW.inv eX.inv eY.inv
    (by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]; exact hf.symm)
    (by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]; exact hg.symm)
  hom_inv_id := gluePair_hom_ext f g (by simp) (by simp)
  inv_hom_id := gluePair_hom_ext f' g' (by simp) (by simp)

variable (iW : W ≅ W') (iX : X ≅ X') (iY : Y ≅ Y') (hf' : f ≫ iX.hom = iW.hom ≫ f')
  (hg' : g ≫ iY.hom = iW.hom ≫ g')

/-- The inverse of `AlgebraicGeometry.Scheme.gluePairCongr` on the first leg is the inverse of
the isomorphism of first pieces followed by the first leg. -/
@[reassoc (attr := simp)]
lemma gluePairInl_gluePairCongr_inv :
    gluePairInl f' g' ≫ (gluePairCongr f g f' g' iW iX iY hf' hg').inv =
      iX.inv ≫ gluePairInl f g :=
  gluePairInl_desc _ _ _ _ _

/-- The inverse of `AlgebraicGeometry.Scheme.gluePairCongr` on the second leg is the inverse of
the isomorphism of second pieces followed by the second leg. -/
@[reassoc (attr := simp)]
lemma gluePairInr_gluePairCongr_inv :
    gluePairInr f' g' ≫ (gluePairCongr f g f' g' iW iX iY hf' hg').inv =
      iY.inv ≫ gluePairInr f g :=
  gluePairInr_desc _ _ _ _ _

section OpensCover

variable {T U : Scheme.{u}} {P₁ P₂ : T.Opens} (hP : P₁ ⊔ P₂ = ⊤) {A B : U.Opens}
  (hAB : A ⊔ B = ⊤) (δ₁ : A.toScheme ≅ P₁.toScheme) (δ₂ : B.toScheme ≅ P₂.toScheme)
  (δW : (A ⊓ B).toScheme ≅ (P₁ ⊓ P₂).toScheme)
  (h₁ : U.homOfLE (inf_le_left : A ⊓ B ≤ A) ≫ δ₁.hom =
    δW.hom ≫ T.homOfLE (inf_le_left : P₁ ⊓ P₂ ≤ P₁))
  (h₂ : U.homOfLE (inf_le_right : A ⊓ B ≤ B) ≫ δ₂.hom =
    δW.hom ≫ T.homOfLE (inf_le_right : P₁ ⊓ P₂ ≤ P₂))

/-- **Two schemes covered by two open subschemes each are isomorphic** as soon as the two pieces
and their overlap are isomorphic compatibly with the inclusions.  No cocycle condition enters,
because the glueing of a pair along an open subscheme is a locally directed colimit. -/
def isoOfOpensCover : T ≅ U :=
  (gluePairOpensDescIso P₁ P₂ hP).symm ≪≫
    (gluePairCongr (U.homOfLE (inf_le_left : A ⊓ B ≤ A))
      (U.homOfLE (inf_le_right : A ⊓ B ≤ B)) (T.homOfLE (inf_le_left : P₁ ⊓ P₂ ≤ P₁))
      (T.homOfLE (inf_le_right : P₁ ⊓ P₂ ≤ P₂)) δW δ₁ δ₂ h₁ h₂).symm ≪≫
    gluePairOpensDescIso A B hAB

/-- The forward map of `AlgebraicGeometry.Scheme.isoOfOpensCover`, as a composite through the
glueings of the two covers. -/
lemma isoOfOpensCover_hom : (isoOfOpensCover hP hAB δ₁ δ₂ δW h₁ h₂).hom =
    (gluePairOpensDescIso P₁ P₂ hP).inv ≫
      (gluePairCongr (U.homOfLE (inf_le_left : A ⊓ B ≤ A))
        (U.homOfLE (inf_le_right : A ⊓ B ≤ B)) (T.homOfLE (inf_le_left : P₁ ⊓ P₂ ≤ P₁))
        (T.homOfLE (inf_le_right : P₁ ⊓ P₂ ≤ P₂)) δW δ₁ δ₂ h₁ h₂).inv ≫
      gluePairOpensDesc A B := rfl

/-- On `P₁`, the isomorphism `AlgebraicGeometry.Scheme.isoOfOpensCover` is `δ₁⁻¹` followed by
the inclusion of `A`. -/
lemma ι_isoOfOpensCover_hom_left :
    P₁.ι ≫ (isoOfOpensCover hP hAB δ₁ δ₂ δW h₁ h₂).hom = δ₁.inv ≫ A.ι := by
  have hι : P₁.ι ≫ (gluePairOpensDescIso P₁ P₂ hP).inv = gluePairOpensInl P₁ P₂ := by
    rw [← gluePairOpensInl_desc P₁ P₂, ← gluePairOpensDescIso_hom P₁ P₂ hP, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [isoOfOpensCover_hom, ← Category.assoc, hι, gluePairInl_gluePairCongr_inv_assoc,
    gluePairOpensInl_desc]

/-- On `P₂`, the isomorphism `AlgebraicGeometry.Scheme.isoOfOpensCover` is `δ₂⁻¹` followed by
the inclusion of `B`. -/
lemma ι_isoOfOpensCover_hom_right :
    P₂.ι ≫ (isoOfOpensCover hP hAB δ₁ δ₂ δW h₁ h₂).hom = δ₂.inv ≫ B.ι := by
  have hι : P₂.ι ≫ (gluePairOpensDescIso P₁ P₂ hP).inv = gluePairOpensInr P₁ P₂ := by
    rw [← gluePairOpensInr_desc P₁ P₂, ← gluePairOpensDescIso_hom P₁ P₂ hP, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [isoOfOpensCover_hom, ← Category.assoc, hι, gluePairInr_gluePairCongr_inv_assoc,
    gluePairOpensInr_desc]

end OpensCover

end Congr

end AlgebraicGeometry.Scheme

namespace Stacks.Etale

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- **A morphism out of a glueing along an open subscheme is étale when its two components
are.** -/
theorem etale_gluePairDesc {W V₁ V₂ : Scheme.{u}} (i₁ : W ⟶ V₁) (i₂ : W ⟶ V₂)
    [IsOpenImmersion i₁] [IsOpenImmersion i₂] (q₁ : V₁ ⟶ Y) (q₂ : V₂ ⟶ Y) [Etale q₁] [Etale q₂]
    (h : i₁ ≫ q₁ = i₂ ≫ q₂) : Etale (gluePairDesc i₁ i₂ q₁ q₂ h) := by
  have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have key : ∀ i : WidePushoutShape WalkingPair,
      Etale (colimit.ι (gluePairDiagram i₁ i₂) i ≫ gluePairDesc i₁ i₂ q₁ q₂ h) := by
    rintro (_ | b)
    · rw [gluePair_ι_none, Category.assoc, gluePairInl_desc]
      infer_instance
    · cases b
      · rw [show colimit.ι (gluePairDiagram i₁ i₂) (some WalkingPair.left) ≫
            gluePairDesc i₁ i₂ q₁ q₂ h = q₁ from gluePairInl_desc i₁ i₂ q₁ q₂ h]
        infer_instance
      · rw [show colimit.ι (gluePairDiagram i₁ i₂) (some WalkingPair.right) ≫
            gluePairDesc i₁ i₂ q₁ q₂ h = q₂ from gluePairInr_desc i₁ i₂ q₁ q₂ h]
        infer_instance
  have hf : ∀ i, (Scheme.IsLocallyDirected.openCover (gluePairDiagram i₁ i₂)).f i =
      colimit.ι (gluePairDiagram i₁ i₂) i := fun _ ↦ rfl
  refine IsZariskiLocalAtSource.of_openCover
    (Scheme.IsLocallyDirected.openCover (gluePairDiagram i₁ i₂)) fun i ↦ ?_
  rw [hf]
  exact key i

section BaseChange

variable (f : X ⟶ Y) {V V' : Scheme.{u}} (q : V ⟶ Y) (q' : V' ⟶ Y) (n : V' ⟶ V)
  (hn : n ≫ q = q')

/-- The canonical morphism of base changes induced by a morphism over `Y`. -/
def baseChangeOver : pullback q' f ⟶ pullback q f :=
  pullback.map q' f q f n (𝟙 X) (𝟙 Y) (by rw [Category.comp_id, hn]) (by simp)

/-- `Stacks.Etale.baseChangeOver` commutes with the second projections to `X`. -/
@[reassoc (attr := simp)]
lemma baseChangeOver_snd : baseChangeOver f q q' n hn ≫ pullback.snd q f = pullback.snd q' f :=
  pullback.lift_snd _ _ _

/-- `Stacks.Etale.baseChangeOver` covers `n` on the first projections. -/
@[reassoc (attr := simp)]
lemma baseChangeOver_fst :
    baseChangeOver f q q' n hn ≫ pullback.fst q f = pullback.fst q' f ≫ n :=
  pullback.lift_fst _ _ _

/-- The base change of a morphism over `Y` is the base change of that morphism along the first
projection. -/
theorem isPullback_baseChangeOver :
    IsPullback (baseChangeOver f q q' n hn) (pullback.fst q' f) (pullback.fst q f) n := by
  refine IsPullback.of_right (h₁₂ := pullback.snd q f) ?_ ?_ (IsPullback.of_hasPullback q f).flip
  · rw [baseChangeOver_snd, hn]
    exact (IsPullback.of_hasPullback q' f).flip
  · simp

/-- The base change of an open immersion over `Y` is an open immersion. -/
instance isOpenImmersion_baseChangeOver [IsOpenImmersion n] :
    IsOpenImmersion (baseChangeOver f q q' n hn) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_baseChangeOver f q q' n hn).flip ‹_›

/-- The range of `Stacks.Etale.baseChangeOver` is the preimage of the range of `n` under the
first projection. -/
lemma range_baseChangeOver :
    Set.range (baseChangeOver f q q' n hn).base =
      (pullback.fst q f).base ⁻¹' Set.range n.base := by
  rw [baseChangeOver, Scheme.Pullback.range_map]
  simp

/-- For an open immersion `n`, the open subscheme cut out by `Stacks.Etale.baseChangeOver` is the
preimage of the image of `n` under the first projection. -/
lemma opensRange_baseChangeOver [IsOpenImmersion n] :
    (baseChangeOver f q q' n hn).opensRange = pullback.fst q f ⁻¹ᵁ n.opensRange :=
  TopologicalSpace.Opens.ext (by
    rw [Scheme.Hom.coe_opensRange, range_baseChangeOver]
    simp [Scheme.Hom.coe_opensRange])

end BaseChange

section Glue

/-- **Descending an open subscheme of a base change.**  Let `f` be a universal homeomorphism and
let the base change of `q : V ⟶ Y` be identified with an open subscheme `A` of a scheme `U` over
`X`.  Then every open subscheme `C` of `U` contained in `A` is cut out by an open subscheme `Z` of
`V`, and the base change of `Z` is identified with `C`. -/
lemma exists_opens_overlap_iso (f : X ⟶ Y) [UniversalHomeomorphism f] {U V : Scheme.{u}}
    (q : V ⟶ Y) {A C : U.Opens} (hC : C ≤ A) (e : pullback q f ≅ A.toScheme) :
    ∃ (Z : V.Opens) (t : pullback (Z.ι ≫ q) f ≅ C.toScheme),
      t.hom ≫ C.ι = baseChangeOver f q (Z.ι ≫ q) Z.ι rfl ≫ e.hom ≫ A.ι := by
  have : UniversalHomeomorphism (pullback.fst q f) := by
    rw [universalHomeomorphism_iff]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback q f).flip ((universalHomeomorphism_iff f).mp inferInstance)
  obtain ⟨Z, hZ, -⟩ := exists_opens_preimage_eq_of_universalHomeomorphism
    (pullback.fst q f) ((e.hom ≫ A.ι) ⁻¹ᵁ C)
  have hrange : (baseChangeOver f q (Z.ι ≫ q) Z.ι rfl ≫ e.hom ≫ A.ι).opensRange = C := by
    rw [Scheme.Hom.opensRange_comp, opensRange_baseChangeOver, Scheme.Opens.opensRange_ι, hZ,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr hC]
  exact ⟨Z, IsOpenImmersion.isoOfRangeEq _ C.ι (range_base_eq_of_opensRange_eq _ hrange),
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩

/-- **Assembling an identification of a base change out of two overlapping pieces.**  Let `U` be
a scheme over `X` covered by two open subschemes `A` and `B`.  If the two pieces and their overlap
are realized as open subschemes of `V ×_Y X` covering it, compatibly with the inclusions and with
the projection to `X`, then `U` is the base change of `V`. -/
lemma exists_pullback_iso_of_opens (f : X ⟶ Y) {U V : Scheme.{u}} (p : U ⟶ X) (q : V ⟶ Y)
    {A B : U.Opens} (hAB : A ⊔ B = ⊤) {P₁ P₂ : (pullback q f).Opens} (hP : P₁ ⊔ P₂ = ⊤)
    (c₁ : A.toScheme ⟶ pullback q f) (c₂ : B.toScheme ⟶ pullback q f)
    (cW : (A ⊓ B).toScheme ⟶ pullback q f)
    [IsOpenImmersion c₁] [IsOpenImmersion c₂] [IsOpenImmersion cW]
    (hr₁ : c₁.opensRange = P₁) (hr₂ : c₂.opensRange = P₂) (hrW : cW.opensRange = P₁ ⊓ P₂)
    (hc₁ : U.homOfLE (inf_le_left : A ⊓ B ≤ A) ≫ c₁ = cW)
    (hc₂ : U.homOfLE (inf_le_right : A ⊓ B ≤ B) ≫ c₂ = cW)
    (hp₁ : c₁ ≫ pullback.snd q f = A.ι ≫ p) (hp₂ : c₂ ≫ pullback.snd q f = B.ι ≫ p) :
    ∃ e : pullback q f ≅ U, e.hom ≫ p = pullback.snd q f := by
  have hrr₁ := range_base_eq_of_opensRange_eq c₁ hr₁
  have hrr₂ := range_base_eq_of_opensRange_eq c₂ hr₂
  have hrrW := range_base_eq_of_opensRange_eq cW hrW
  have hf₁ := IsOpenImmersion.isoOfRangeEq_hom_fac c₁ P₁.ι hrr₁
  have hf₂ := IsOpenImmersion.isoOfRangeEq_hom_fac c₂ P₂.ι hrr₂
  have hfW := IsOpenImmersion.isoOfRangeEq_hom_fac cW (P₁ ⊓ P₂).ι hrrW
  have hle : ∀ {A' : U.Opens} {P' : (pullback q f).Opens} (c : A'.toScheme ⟶ pullback q f)
      [IsOpenImmersion c] (hrr : Set.range c.base = Set.range P'.ι.base) (hA : A ⊓ B ≤ A')
      (hP' : P₁ ⊓ P₂ ≤ P'), U.homOfLE hA ≫ c = cW →
      U.homOfLE hA ≫ (IsOpenImmersion.isoOfRangeEq c P'.ι hrr).hom =
      (IsOpenImmersion.isoOfRangeEq cW (P₁ ⊓ P₂).ι hrrW).hom ≫ (pullback q f).homOfLE hP' := by
    intro A' P' c _ hrr hA hP' hc
    rw [← cancel_mono P'.ι]
    simp only [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Scheme.homOfLE_ι, hfW, hc]
  have h₁ := hle c₁ hrr₁ inf_le_left inf_le_left hc₁
  have h₂ := hle c₂ hrr₂ inf_le_right inf_le_right hc₂
  refine ⟨Scheme.isoOfOpensCover hP hAB (IsOpenImmersion.isoOfRangeEq c₁ P₁.ι hrr₁)
    (IsOpenImmersion.isoOfRangeEq c₂ P₂.ι hrr₂)
    (IsOpenImmersion.isoOfRangeEq cW (P₁ ⊓ P₂).ι hrrW) h₁ h₂, ?_⟩
  have := Scheme.isIso_gluePairOpensDesc P₁ P₂ hP
  rw [← cancel_epi (Scheme.gluePairOpensDesc P₁ P₂)]
  refine Scheme.gluePair_hom_ext _ _ ?_ ?_
  · simp only [← Category.assoc, Scheme.gluePairOpensInl_desc]
    rw [Scheme.ι_isoOfOpensCover_hom_left, Category.assoc, ← hp₁, ← Category.assoc,
      (Iso.inv_comp_eq _).mpr hf₁.symm]
  · simp only [← Category.assoc, Scheme.gluePairOpensInr_desc]
    rw [Scheme.ι_isoOfOpensCover_hom_right, Category.assoc, ← hp₂, ← Category.assoc,
      (Iso.inv_comp_eq _).mpr hf₂.symm]

/-- The identification of the overlap with a base change is compatible with the projection to the
base and with the inclusion of the overlap into the piece. -/
private theorem overlap_iso_compat (f : X ⟶ Y) {U V : Scheme.{u}} (p : U ⟶ X) (q : V ⟶ Y)
    {A C : U.Opens} (hC : C ≤ A) (e : pullback q f ≅ A.toScheme)
    (he : e.hom ≫ (A.ι ≫ p) = pullback.snd q f) {Z : V.Opens}
    {t : pullback (Z.ι ≫ q) f ≅ C.toScheme}
    (ht : t.hom ≫ C.ι = baseChangeOver f q (Z.ι ≫ q) Z.ι rfl ≫ e.hom ≫ A.ι) :
    t.inv ≫ pullback.snd (Z.ι ≫ q) f = C.ι ≫ p ∧
      U.homOfLE hC ≫ e.inv = t.inv ≫ baseChangeOver f q (Z.ι ≫ q) Z.ι rfl := by
  refine ⟨?_, ?_⟩
  · rw [Iso.inv_comp_eq, ← Category.assoc, ht, Category.assoc, Category.assoc, he,
      baseChangeOver_snd]
  · rw [← cancel_mono (e.hom ≫ A.ι), Category.assoc, Category.assoc, ← Category.assoc e.inv,
      e.inv_hom_id, Category.id_comp, Scheme.homOfLE_ι, ← ht, ← Category.assoc,
      t.inv_hom_id, Category.id_comp]

/-- **The essential image of base change on étale schemes is closed under glueing along an open
subscheme.**  Let `f : X ⟶ Y` be a universal homeomorphism and let `U` be a scheme over `X`
covered by two open subschemes `A` and `B`.  If each of `A` and `B` is, over `X`, the base change
along `f` of a scheme étale over `Y`, then so is `U`.

The hypotheses and the conclusion are in the elementary form consumed by
`Stacks.Etale.essSurj_etalePullback_of_forall_exists_pullback_iso`.  Nothing is assumed about the
overlap: it is descended from either piece, and the two descents are identified by the rigidity
of `Stacks.Etale.exists_iso_of_pullback_iso`, so no cocycle condition has to be checked. -/
theorem exists_etale_pullback_iso_of_sup_opens (f : X ⟶ Y) [UniversalHomeomorphism f]
    {U : Scheme.{u}} (p : U ⟶ X) (A B : U.Opens) (hAB : A ⊔ B = ⊤)
    (h₁ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ A.toScheme),
      e.hom ≫ (A.ι ≫ p) = pullback.snd q f)
    (h₂ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ B.toScheme),
      e.hom ≫ (B.ι ≫ p) = pullback.snd q f) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f := by
  obtain ⟨V₁, q₁, hq₁, e₁, he₁⟩ := h₁
  obtain ⟨V₂, q₂, hq₂, e₂, he₂⟩ := h₂
  have hE₁ : Etale q₁ := hq₁
  have hE₂ : Etale q₂ := hq₂
  obtain ⟨Z₁, t₁, ht₁⟩ := exists_opens_overlap_iso f q₁ (inf_le_left : A ⊓ B ≤ A) e₁
  obtain ⟨Z₂, t₂, ht₂⟩ := exists_opens_overlap_iso f q₂ (inf_le_right : A ⊓ B ≤ B) e₂
  obtain ⟨hsW₁, hkey₁⟩ := overlap_iso_compat f p q₁ inf_le_left e₁ he₁ ht₁
  obtain ⟨hsW₂, hkey₂⟩ := overlap_iso_compat f p q₂ inf_le_right e₂ he₂ ht₂
  obtain ⟨d, hdq, hdfst⟩ := exists_iso_of_pullback_iso f (Z₁.ι ≫ q₁) (Z₂.ι ≫ q₂)
    (t₁ ≪≫ t₂.symm) (by
      rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hsW₂]
      exact ((Iso.inv_comp_eq _).mp hsW₁).symm)
  have hdfst' : pullback.fst (Z₁.ι ≫ q₁) f ≫ d.hom =
      t₁.hom ≫ t₂.inv ≫ pullback.fst (Z₂.ι ≫ q₂) f := by
    rw [hdfst, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have hcompat : Z₁.ι ≫ q₁ = (d.hom ≫ Z₂.ι) ≫ q₂ := by rw [Category.assoc]; exact hdq.symm
  have hn₁ : gluePairInl Z₁.ι (d.hom ≫ Z₂.ι) ≫
      gluePairDesc Z₁.ι (d.hom ≫ Z₂.ι) q₁ q₂ hcompat = q₁ := gluePairInl_desc _ _ _ _ _
  have hn₂ : gluePairInr Z₁.ι (d.hom ≫ Z₂.ι) ≫
      gluePairDesc Z₁.ι (d.hom ≫ Z₂.ι) q₁ q₂ hcompat = q₂ := gluePairInr_desc _ _ _ _ _
  have hnW : (Z₁.ι ≫ gluePairInl Z₁.ι (d.hom ≫ Z₂.ι)) ≫
      gluePairDesc Z₁.ι (d.hom ≫ Z₂.ι) q₁ q₂ hcompat = Z₁.ι ≫ q₁ := by
    rw [Category.assoc, hn₁]
  -- the two pieces, as open subschemes of the base change of the glueing
  have hA := (Iso.inv_comp_eq e₁).mpr he₁.symm
  have hB := (Iso.inv_comp_eq e₂).mpr he₂.symm
  refine ⟨gluePair Z₁.ι (d.hom ≫ Z₂.ι), gluePairDesc Z₁.ι (d.hom ≫ Z₂.ι) q₁ q₂ hcompat,
    etale_gluePairDesc _ _ _ _ hcompat, ?_⟩
  obtain ⟨E, hE⟩ := exists_pullback_iso_of_opens f p
      (gluePairDesc Z₁.ι (d.hom ≫ Z₂.ι) q₁ q₂ hcompat) hAB
      (P₁ := pullback.fst (gluePairDesc Z₁.ι (d.hom ≫ Z₂.ι) q₁ q₂ hcompat) f ⁻¹ᵁ
        (gluePairInl Z₁.ι (d.hom ≫ Z₂.ι)).opensRange)
      (P₂ := pullback.fst (gluePairDesc Z₁.ι (d.hom ≫ Z₂.ι) q₁ q₂ hcompat) f ⁻¹ᵁ
        (gluePairInr Z₁.ι (d.hom ≫ Z₂.ι)).opensRange)
      (by
        show pullback.fst _ f ⁻¹ᵁ ((gluePairInl Z₁.ι (d.hom ≫ Z₂.ι)).opensRange ⊔
          (gluePairInr Z₁.ι (d.hom ≫ Z₂.ι)).opensRange) = ⊤
        rw [gluePair_opensRange_sup]
        rfl)
      (e₁.inv ≫ baseChangeOver f _ q₁ (gluePairInl Z₁.ι (d.hom ≫ Z₂.ι)) hn₁)
      (e₂.inv ≫ baseChangeOver f _ q₂ (gluePairInr Z₁.ι (d.hom ≫ Z₂.ι)) hn₂)
      (t₁.inv ≫ baseChangeOver f _ (Z₁.ι ≫ q₁) (Z₁.ι ≫ gluePairInl Z₁.ι (d.hom ≫ Z₂.ι)) hnW)
      (by rw [Scheme.Hom.opensRange_comp_of_isIso, opensRange_baseChangeOver])
      (by rw [Scheme.Hom.opensRange_comp_of_isIso, opensRange_baseChangeOver])
      (by
        rw [Scheme.Hom.opensRange_comp_of_isIso, opensRange_baseChangeOver,
          ← gluePair_opensRange_inf]
        rfl)
      (by
        refine pullback.hom_ext ?_ ?_
        · simp only [Category.assoc, baseChangeOver_fst]
          rw [← Category.assoc (U.homOfLE _), hkey₁]
          simp only [Category.assoc, baseChangeOver_fst_assoc]
        · simp only [Category.assoc, baseChangeOver_snd]
          rw [hA, hsW₁, ← Category.assoc, Scheme.homOfLE_ι])
      (by
        refine pullback.hom_ext ?_ ?_
        · simp only [Category.assoc, baseChangeOver_fst]
          rw [← Category.assoc (U.homOfLE _), hkey₂]
          simp only [Category.assoc, baseChangeOver_fst_assoc]
          rw [gluePair_condition]
          simp only [Category.assoc]
          rw [← Category.assoc (pullback.fst (Z₁.ι ≫ q₁) f) d.hom, hdfst']
          simp only [Category.assoc]
          rw [← Category.assoc t₁.inv, t₁.inv_hom_id, Category.id_comp]
        · simp only [Category.assoc, baseChangeOver_snd]
          rw [hB, hsW₁, ← Category.assoc, Scheme.homOfLE_ι])
      (by simp only [Category.assoc, baseChangeOver_snd]; rw [hA])
      (by simp only [Category.assoc, baseChangeOver_snd]; rw [hB])
  exact ⟨E, hE⟩

/-- A base change identification of the source of an open immersion restricts to its image. -/
private theorem exists_etale_pullback_iso_opensRange (f : X ⟶ Y) {U U' : Scheme.{u}} (p : U ⟶ X)
    (j : U' ⟶ U) [IsOpenImmersion j]
    (h : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U'),
      e.hom ≫ (j ≫ p) = pullback.snd q f) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ j.opensRange.toScheme),
      e.hom ≫ (j.opensRange.ι ≫ p) = pullback.snd q f := by
  obtain ⟨V, q, hq, e, he⟩ := h
  exact ⟨V, q, hq, e ≪≫ j.isoOpensRange, by
    rw [Iso.trans_hom, Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, he]⟩

/-- **The essential image of base change on étale schemes is closed under glueing along an open
subscheme**, stated for a pair of open immersions whose images cover. -/
theorem exists_etale_pullback_iso_of_sup_opensRange (f : X ⟶ Y) [UniversalHomeomorphism f]
    {U U₁ U₂ : Scheme.{u}} (p : U ⟶ X) (j₁ : U₁ ⟶ U) (j₂ : U₂ ⟶ U)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hj : j₁.opensRange ⊔ j₂.opensRange = ⊤)
    (h₁ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U₁),
      e.hom ≫ (j₁ ≫ p) = pullback.snd q f)
    (h₂ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U₂),
      e.hom ≫ (j₂ ≫ p) = pullback.snd q f) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f := by
  exact exists_etale_pullback_iso_of_sup_opens f p j₁.opensRange j₂.opensRange hj
    (exists_etale_pullback_iso_opensRange f p j₁ h₁)
    (exists_etale_pullback_iso_opensRange f p j₂ h₂)

/-- **The essential image of base change on étale schemes is closed under glueing two schemes
along a common open subscheme.**  Let `f : X ⟶ Y` be a universal homeomorphism and let
`i₁ : W ⟶ U₁` and `i₂ : W ⟶ U₂` be open immersions.  If each of `U₁` and `U₂` is, over `X`, the
base change along `f` of a scheme étale over `Y`, then so is the glueing of `U₁` and `U₂` along
`W`.

Nothing is assumed about `W`: its descent is read off either piece, and the two readings are
identified by rigidity, so there is no cocycle condition. -/
theorem exists_etale_pullback_iso_of_gluePair (f : X ⟶ Y) [UniversalHomeomorphism f]
    {W U₁ U₂ : Scheme.{u}} (i₁ : W ⟶ U₁) (i₂ : W ⟶ U₂)
    [IsOpenImmersion i₁] [IsOpenImmersion i₂] (p : gluePair i₁ i₂ ⟶ X)
    (h₁ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U₁),
      e.hom ≫ (gluePairInl i₁ i₂ ≫ p) = pullback.snd q f)
    (h₂ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U₂),
      e.hom ≫ (gluePairInr i₁ i₂ ≫ p) = pullback.snd q f) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ gluePair i₁ i₂),
      e.hom ≫ p = pullback.snd q f :=
  exists_etale_pullback_iso_of_sup_opensRange f p (gluePairInl i₁ i₂) (gluePairInr i₁ i₂)
    (gluePair_opensRange_sup i₁ i₂) h₁ h₂

end Glue

end Stacks.Etale

end

end
