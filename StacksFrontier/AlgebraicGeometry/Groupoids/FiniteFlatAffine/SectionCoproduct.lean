module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.CoproductCriterion
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.CoproductEtale
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantOpenSubgroupoid

/-!
# The sheet of a section of `U' ⟶ U` is a copy of `G` inside `G'`

Let `F : G' ⟶ G` be a morphism of groupoid schemes whose source square is cartesian, and let
`σ : U ⟶ U'` be a section of `f : U' ⟶ U` which is an open immersion with closed image whose
image `V = range σ` is an *invariant* open of `U'`. Then:

* `G'` is the **disjoint union** of the groupoid scheme `G₁` carried by `V` and the one carried by
  the complementary open, because the two object opens are complementary and so are the two arrow
  opens;
* `G₁` has **the same invariant ring as `G`**: the composite `C → C' → C₁` is bijective.

Consequently the map on invariant rings `C → C'` is **étale at every point of the piece `Spec C₁`
of `Spec C'`**, with no hypothesis whatever on the complementary piece.

This is the geometric half of the "Claim" in the proof of [Stacks Project, Tag 0DT9], turned into
the hypothesis of
`AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_invariantRingMap_of_etale_left`.

## Main results

* `AlgebraicGeometry.comp_section_eq_of_range_subset`: a morphism whose image lies in the sheet of
  a section factors as its composite with the retraction followed by the section.
* `AlgebraicGeometry.GroupoidScheme.isIso_liftSection`: **the sheet of the section is isomorphic to
  `U`**, by the section and the retraction.
* `AlgebraicGeometry.GroupoidScheme.arrowSection`: **the induced section `R ⟶ R'` on arrow
  schemes**, obtained from the cartesian source square; this is the only place the source square
  is used as a *pullback* rather than merely a commuting square.
* `AlgebraicGeometry.GroupoidScheme.isIso_liftArrowSection`: the arrows of the sheet are
  isomorphic to `R`.
* `AlgebraicGeometry.GroupoidScheme.bijective_invariantRingMap_comp_restrictInvariantOpenHom`:
  **the invariant ring of the sheet is the invariant ring of `G`**.
* `AlgebraicGeometry.GroupoidScheme.isCoproductDecomposition_restrictInvariantOpen_section`:
  **`G'` is the disjoint union of the sheet and its complement**.
* `AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_invariantRingMap_of_section`: **the map on
  invariant rings is étale at every point of the sheet's piece of `Spec C'`**.

## Implementation notes

The sheet is packaged with `Stacks.Groupoids.restrictInvariantOpen` rather than by building a
morphism of groupoid schemes `G ⟶ G'` by hand: `Stacks.Groupoids.InvariantOpenSubgroupoid` already
proves the five compatibility equations, including the one for the composition morphism, which is
by far the most expensive. The price is that the invariant ring of the sheet has to be *identified*
with that of `G` instead of being equal to it, and that identification is
`bijective_invariantRingMap_comp_restrictInvariantOpenHom`.

Surjectivity of that identification is the only step that needs the section on *arrow* schemes:
an invariant function on the sheet pulls back along the isomorphism `U ≅ V` to a function on `U`,
and that function is invariant because `R ≅ s'⁻¹(V)` compatibly with source and target.

## References

* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry

/-- **A morphism whose image lies in the sheet of a section factors through the section**, and the
factorisation is its composite with the retraction. -/
theorem comp_section_eq_of_range_subset {X Y T : Scheme.{u}} {σ : X ⟶ Y} [IsOpenImmersion σ]
    {f : Y ⟶ X} (hσ : σ ≫ f = 𝟙 X) (h : T ⟶ Y)
    (hr : Set.range h.base ⊆ Set.range σ.base) : (h ≫ f) ≫ σ = h := by
  rw [← IsOpenImmersion.lift_fac σ h hr]
  simp only [Category.assoc, reassoc_of% hσ]

namespace GroupoidScheme

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)

/-! ### The sheet of the section, as an open subscheme isomorphic to `U` -/

section Objects

variable {σ : G.objects.left ⟶ G'.objects.left} [IsOpenImmersion σ]

/-- The section read as a morphism into the open subscheme of `U'` it cuts out. -/
def liftSection (σ : G.objects.left ⟶ G'.objects.left) [IsOpenImmersion σ] :
    G.objects.left ⟶ σ.opensRange.toScheme :=
  IsOpenImmersion.lift σ.opensRange.ι σ (by simp)

/-- The lift of `σ` to its open range, followed by the inclusion of that range, is `σ`. -/
@[reassoc (attr := simp)]
theorem liftSection_ι : liftSection σ ≫ σ.opensRange.ι = σ :=
  IsOpenImmersion.lift_fac _ _ _

/-- If `σ` is a section of `f`, the lift of `σ` to its range followed by the restriction of `f`
to that range is the identity of `U`. -/
theorem liftSection_comp (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left) :
    liftSection σ ≫ σ.opensRange.ι ≫ F.mapObjects.left = 𝟙 G.objects.left := by
  rw [← Category.assoc, liftSection_ι, hσ]

/-- If `σ` is a section of `f`, the restriction of `f` to the range of `σ` followed by the lift
of `σ` is the identity of that range. -/
theorem comp_liftSection (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left) :
    (σ.opensRange.ι ≫ F.mapObjects.left) ≫ liftSection σ = 𝟙 σ.opensRange.toScheme := by
  rw [← cancel_mono σ.opensRange.ι, Category.id_comp, Category.assoc, liftSection_ι]
  exact comp_section_eq_of_range_subset hσ σ.opensRange.ι (by simp)

/-- **The sheet of a section of `f : U' ⟶ U` is isomorphic to `U`**, the inverse isomorphism being
the restriction of `f` to that sheet. -/
theorem isIso_liftSection (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left) :
    IsIso (liftSection σ) :=
  ⟨⟨σ.opensRange.ι ≫ F.mapObjects.left, by
      simpa only [Category.assoc] using liftSection_comp F hσ, comp_liftSection F hσ⟩⟩

end Objects

/-! ### The section on arrow schemes -/

section Arrows

variable {σ : G.objects.left ⟶ G'.objects.left} [IsOpenImmersion σ]

/-- **The section on arrow schemes induced by a section on object schemes.** It exists because the
source square of `F` is cartesian: an arrow of `R` together with the point `σ(s(r))` of `U'` over
`s(r)` is an arrow of `R'`.

This is the only use made of the source square as a *pullback*; all the other compatibilities need
no more than that it commutes. -/
def arrowSection
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left) : G.arrows.left ⟶ G'.arrows.left :=
  hsource.lift (𝟙 G.arrows.left) (G.source.left ≫ σ) (by
    rw [Category.id_comp, Category.assoc, hσ, Category.comp_id])

omit [IsOpenImmersion σ] in
/-- The induced section on arrow schemes is a section of the map `R' ⟶ R` of `F`. -/
@[reassoc (attr := simp)]
theorem arrowSection_comp_mapArrows
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left) :
    arrowSection F hsource hσ ≫ F.mapArrows.left = 𝟙 G.arrows.left :=
  hsource.lift_fst _ _ _

omit [IsOpenImmersion σ] in
/-- The induced section on arrow schemes is compatible with the source morphisms:
`ρ ≫ s' = s ≫ σ`. -/
@[reassoc (attr := simp)]
theorem arrowSection_comp_source
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left) :
    arrowSection F hsource hσ ≫ G'.source.left = G.source.left ≫ σ :=
  hsource.lift_snd _ _ _

/-- The source of the image of an arrow under the induced section lies in the range of `σ`. -/
theorem mem_opensRange_source_arrowSection
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left) (r : G.arrows.left) :
    G'.source.left.base ((arrowSection F hsource hσ).base r) ∈ σ.opensRange := by
  have h := congrArg (fun k : G.arrows.left ⟶ G'.objects.left => k.base r)
    (arrowSection_comp_source F hsource hσ)
  simp only [Scheme.Hom.comp_apply] at h
  rw [h]
  exact ⟨G.source.left.base r, rfl⟩

/-- **The induced section on arrow schemes is compatible with the target morphisms.** The composite
`ρ ≫ t'` lands in the sheet of `σ`, by invariance of that sheet, so it factors through `σ`; and its
composite with `f` is `t`, because `F` commutes with the target morphisms. -/
theorem arrowSection_comp_target
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left)
    (hV : IsInvariantOpen G' σ.opensRange) :
    arrowSection F hsource hσ ≫ G'.target.left = G.target.left ≫ σ := by
  have hwt : F.mapArrows.left ≫ G.target.left = G'.target.left ≫ F.mapObjects.left := by
    rw [← Over.comp_left, ← Over.comp_left, F.map_target]
  have hr : Set.range (arrowSection F hsource hσ ≫ G'.target.left).base ⊆
      Set.range σ.base := by
    rintro y ⟨r, rfl⟩
    exact hV _ (mem_opensRange_source_arrowSection F hsource hσ r)
  have hfo : (arrowSection F hsource hσ ≫ G'.target.left) ≫ F.mapObjects.left =
      G.target.left := by
    rw [Category.assoc, ← hwt, ← Category.assoc, arrowSection_comp_mapArrows, Category.id_comp]
  simpa only [hfo] using
    (comp_section_eq_of_range_subset hσ (arrowSection F hsource hσ ≫ G'.target.left) hr).symm

/-- The induced section on arrow schemes, read as a morphism into the open `s'⁻¹(V)` of `R'`. -/
def liftArrowSection
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left) :
    G.arrows.left ⟶ (invariantArrows G' σ.opensRange).toScheme :=
  IsOpenImmersion.lift (invariantArrows G' σ.opensRange).ι (arrowSection F hsource hσ)
    (range_subset_range_ι _ _ (mem_opensRange_source_arrowSection F hsource hσ))

/-- The lift of the induced section to `s'⁻¹(V)`, followed by the inclusion of `s'⁻¹(V)`, is the
induced section. -/
@[reassoc (attr := simp)]
theorem liftArrowSection_ι
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left) :
    liftArrowSection F hsource hσ ≫ (invariantArrows G' σ.opensRange).ι =
      arrowSection F hsource hσ :=
  IsOpenImmersion.lift_fac _ _ _

/-- The lift of the induced section to `s'⁻¹(V)` followed by the restriction of `R' ⟶ R` to
`s'⁻¹(V)` is the identity of `R`. -/
theorem liftArrowSection_comp
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left) :
    liftArrowSection F hsource hσ ≫
        (invariantArrows G' σ.opensRange).ι ≫ F.mapArrows.left = 𝟙 G.arrows.left := by
  rw [← Category.assoc, liftArrowSection_ι, arrowSection_comp_mapArrows]

/-- When the range `V` of `σ` is invariant, the restriction of `R' ⟶ R` to `s'⁻¹(V)` followed by
the lift of the induced section is the identity of `s'⁻¹(V)`. -/
theorem comp_liftArrowSection
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left)
    (_hV : IsInvariantOpen G' σ.opensRange) :
    ((invariantArrows G' σ.opensRange).ι ≫ F.mapArrows.left) ≫ liftArrowSection F hsource hσ =
      𝟙 (invariantArrows G' σ.opensRange).toScheme := by
  rw [← cancel_mono (invariantArrows G' σ.opensRange).ι, Category.id_comp, Category.assoc,
    liftArrowSection_ι]
  refine hsource.hom_ext ?_ ?_
  · rw [Category.assoc, arrowSection_comp_mapArrows, Category.comp_id]
  · simp only [Category.assoc, arrowSection_comp_source, reassoc_of% hsource.w]
    simpa only [Category.assoc] using comp_section_eq_of_range_subset hσ
      ((invariantArrows G' σ.opensRange).ι ≫ G'.source.left) (by
        rintro y ⟨x, rfl⟩
        exact x.2)

/-- **The arrows of the sheet of a section are isomorphic to the arrows of `G`.** -/
theorem isIso_liftArrowSection
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left)
    (hV : IsInvariantOpen G' σ.opensRange) :
    IsIso (liftArrowSection F hsource hσ) :=
  ⟨⟨(invariantArrows G' σ.opensRange).ι ≫ F.mapArrows.left, by
      simpa only [Category.assoc] using liftArrowSection_comp F hsource hσ,
    comp_liftArrowSection F hsource hσ hV⟩⟩

/-! ### Compatibility with the structure morphisms of the sheet -/

/-- The isomorphism `R ≅ s'⁻¹(V)` carries the source morphism of the sheet to the source
morphism of `G`, read through `U ≅ V`. -/
theorem liftArrowSection_comp_invariantSource
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left) :
    liftArrowSection F hsource hσ ≫ (invariantSource G' σ.opensRange).left =
      G.source.left ≫ liftSection σ := by
  have hι : (invariantSource G' σ.opensRange).left ≫ σ.opensRange.ι =
      (invariantArrows G' σ.opensRange).ι ≫ G'.source.left := by
    simpa only [Over.comp_left, openOverι_left] using
      congrArg Over.Hom.left (invariantSource_ι G' σ.opensRange)
  rw [← cancel_mono σ.opensRange.ι, Category.assoc, hι, Category.assoc, liftSection_ι,
    ← Category.assoc, liftArrowSection_ι, arrowSection_comp_source]

/-- The isomorphism `R ≅ s'⁻¹(V)` carries the target morphism of the sheet to the target
morphism of `G`, read through `U ≅ V`. -/
theorem liftArrowSection_comp_invariantTarget
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left)
    (hV : IsInvariantOpen G' σ.opensRange) :
    liftArrowSection F hsource hσ ≫ (invariantTarget G' σ.opensRange hV).left =
      G.target.left ≫ liftSection σ := by
  have hι : (invariantTarget G' σ.opensRange hV).left ≫ σ.opensRange.ι =
      (invariantArrows G' σ.opensRange).ι ≫ G'.target.left := by
    simpa only [Over.comp_left, openOverι_left] using
      congrArg Over.Hom.left (invariantTarget_ι G' σ.opensRange hV)
  rw [← cancel_mono σ.opensRange.ι, Category.assoc, hι, Category.assoc, liftSection_ι,
    ← Category.assoc, liftArrowSection_ι, arrowSection_comp_target F hsource hσ hV]

end Arrows

/-! ### The invariant ring of the sheet -/

section InvariantRing

variable {σ : G.objects.left ⟶ G'.objects.left} [IsOpenImmersion σ]

/-- **The invariant ring of the sheet of a section is the invariant ring of `G`.** The composite
`C → C' → C₁` is the corestriction of the isomorphism `Γ(V, ⊤) ≅ Γ(U, ⊤)`, hence injective;
surjective because an invariant function on the sheet pulls back to an invariant function on `U`,
the isomorphism `R ≅ s'⁻¹(V)` carrying the source and target morphisms of the sheet to those of
`G`. -/
theorem bijective_invariantRingMap_comp_restrictInvariantOpenHom
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left)
    (hV : IsInvariantOpen G' σ.opensRange) :
    Function.Bijective
      ((invariantRingMap (restrictInvariantOpenHom G' σ.opensRange hV)).comp
        (invariantRingMap F)) := by
  have hcoe : ∀ c : invariantRing G,
      (((invariantRingMap (restrictInvariantOpenHom G' σ.opensRange hV)).comp
            (invariantRingMap F)) c).1 =
        (σ.opensRange.ι ≫ F.mapObjects.left).appTop.hom c.1 :=
    fun c => invariantRingMap_comp_coe F (restrictInvariantOpenHom G' σ.opensRange hV) c
  have hA : ∀ a : Γ(G.objects.left, ⊤),
      (liftSection σ).appTop.hom
          ((σ.opensRange.ι ≫ F.mapObjects.left).appTop.hom a) = a := by
    intro a
    have h : (liftSection σ ≫ σ.opensRange.ι ≫ F.mapObjects.left).appTop.hom a = a := by
      rw [liftSection_comp F hσ]
      simp
    rwa [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
  have hB : ∀ b : Γ(σ.opensRange.toScheme, ⊤),
      (σ.opensRange.ι ≫ F.mapObjects.left).appTop.hom ((liftSection σ).appTop.hom b) = b := by
    intro b
    have h : ((σ.opensRange.ι ≫ F.mapObjects.left) ≫ liftSection σ).appTop.hom b = b := by
      rw [comp_liftSection F hσ]
      simp
    rwa [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
  have hs' : ∀ b : Γ(σ.opensRange.toScheme, ⊤),
      G.source.left.appTop.hom ((liftSection σ).appTop.hom b) =
        (liftArrowSection F hsource hσ).appTop.hom
          ((invariantSource G' σ.opensRange).left.appTop.hom b) := by
    intro b
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using
      congrArg (fun k : G.arrows.left ⟶ σ.opensRange.toScheme => k.appTop.hom b)
        (liftArrowSection_comp_invariantSource F hsource hσ).symm
  have ht' : ∀ b : Γ(σ.opensRange.toScheme, ⊤),
      G.target.left.appTop.hom ((liftSection σ).appTop.hom b) =
        (liftArrowSection F hsource hσ).appTop.hom
          ((invariantTarget G' σ.opensRange hV).left.appTop.hom b) := by
    intro b
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using
      congrArg (fun k : G.arrows.left ⟶ σ.opensRange.toScheme => k.appTop.hom b)
        (liftArrowSection_comp_invariantTarget F hsource hσ hV).symm
  refine ⟨fun c c' hcc => Subtype.ext ?_, ?_⟩
  · have h1 : (σ.opensRange.ι ≫ F.mapObjects.left).appTop.hom c.1 =
        (σ.opensRange.ι ≫ F.mapObjects.left).appTop.hom c'.1 := by
      rw [← hcoe, ← hcoe, hcc]
    exact ((hA _).symm.trans
      (congrArg (fun z => (liftSection σ).appTop.hom z) h1)).trans (hA _)
  · rintro ⟨bv, hbv⟩
    have hbv' : (invariantSource G' σ.opensRange).left.appTop.hom bv =
        (invariantTarget G' σ.opensRange hV).left.appTop.hom bv := hbv
    refine ⟨⟨(liftSection σ).appTop.hom bv, ?_⟩, Subtype.ext ((hcoe _).trans (hB _))⟩
    show G.source.left.appTop.hom ((liftSection σ).appTop.hom bv) =
      G.target.left.appTop.hom ((liftSection σ).appTop.hom bv)
    rw [hs' bv, ht' bv, hbv']

end InvariantRing

/-! ### The disjoint union decomposition and étaleness on the sheet -/

section Coproduct

variable {σ : G.objects.left ⟶ G'.objects.left} [IsOpenImmersion σ]

/-- The open complement of the sheet of a section whose image is closed. -/
def sectionComplement (σ : G.objects.left ⟶ G'.objects.left) [IsOpenImmersion σ]
    (hcl : IsClosed (Set.range σ.base)) : G'.objects.left.Opens :=
  ⟨(Set.range σ.base)ᶜ, hcl.isOpen_compl⟩

/-- The range of `σ` and `sectionComplement σ hcl` are complementary opens of `U'`. -/
theorem isCompl_opensRange_sectionComplement (hcl : IsClosed (Set.range σ.base)) :
    IsCompl σ.opensRange (sectionComplement σ hcl) := by
  constructor
  · refine disjoint_iff.mpr (TopologicalSpace.Opens.ext ?_)
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hmem : x ∈ (σ.opensRange ⊓ sectionComplement σ hcl : G'.objects.left.Opens) := hx
    exact hmem.2 hmem.1
  · refine codisjoint_iff.mpr (TopologicalSpace.Opens.ext ?_)
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    show x ∈ (σ.opensRange ⊔ sectionComplement σ hcl : G'.objects.left.Opens)
    exact em (x ∈ Set.range σ.base)

/-- **`G'` is the disjoint union of the sheet of a section and its complement.** The sheet is
clopen and invariant, so its complement is an invariant open too, and the two maps on object
schemes — and the two maps on arrow schemes — are open immersions with complementary ranges. -/
theorem isCoproductDecomposition_restrictInvariantOpen_section
    (hcl : IsClosed (Set.range σ.base)) (hV : IsInvariantOpen G' σ.opensRange) :
    IsCoproductDecomposition (restrictInvariantOpenHom G' σ.opensRange hV)
      (restrictInvariantOpenHom G' (sectionComplement σ hcl)
        (isInvariantOpen_of_isCompl G' σ.opensRange (sectionComplement σ hcl)
          (isCompl_opensRange_sectionComplement hcl) hV)) :=
  isCoproductDecomposition_of_isCompl _ _
    (isCompl_opensRange_mapObjects G' σ.opensRange (sectionComplement σ hcl)
      (isCompl_opensRange_sectionComplement hcl) hV)
    (isCompl_opensRange_mapArrows G' σ.opensRange (sectionComplement σ hcl)
      (isCompl_opensRange_sectionComplement hcl) hV)

/-- **The map on invariant rings is étale at every point of the sheet's piece of `Spec C'`.**
The sheet is a piece of a disjoint union decomposition of `G'`, and its invariant ring is that of
`G`, so the composite `Spec C₁ ⟶ Spec C' ⟶ Spec C` is an isomorphism. Nothing is assumed about the
complementary piece. -/
theorem etaleAt_specMap_invariantRingMap_of_section
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left)
    (hcl : IsClosed (Set.range σ.base)) (hV : IsInvariantOpen G' σ.opensRange)
    (x : Spec (.of (invariantRing (restrictInvariantOpen G' σ.opensRange hV)))) :
    EtaleAt (Spec.map (CommRingCat.ofHom (invariantRingMap F)))
      ((Spec.map (CommRingCat.ofHom
        (invariantRingMap (restrictInvariantOpenHom G' σ.opensRange hV)))).base x) := by
  have hiso : IsIso (CommRingCat.ofHom
      ((invariantRingMap (restrictInvariantOpenHom G' σ.opensRange hV)).comp
        (invariantRingMap F))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_invariantRingMap_comp_restrictInvariantOpenHom F hsource hσ hV)
  refine etaleAt_specMap_invariantRingMap_of_etale_left F _ _
    (isCoproductDecomposition_restrictInvariantOpen_section hcl hV) ?_ x
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  infer_instance

end Coproduct

end GroupoidScheme

end AlgebraicGeometry

end

end
