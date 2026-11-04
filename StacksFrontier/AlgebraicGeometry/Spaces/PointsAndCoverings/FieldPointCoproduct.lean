module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCountable
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.PreRelationTestPoints

/-!
# A field-valued point meets only one summand of a coproduct

The spectrum of a field is connected, so a point of an algebraic space with values in a field
cannot be spread over two summands of a coproduct. This file proves the two forms of that
statement.

Let `B` be an algebraic space over a scheme `S` of a big fppf site and let `p` be a field-valued
point of `B`, with representable algebraic space `R` over `B`. If `R` is exhibited as a countable
coproduct of algebraic spaces over `B`, then the inclusion of one of the summands has a section;
and if a morphism `R ⟶ V` of algebraic spaces over `B` is given together with a countable family
over `V` whose fibre products with it exhaust `R`, then the morphism factors through one member
of the family.

Both statements rest on the same geometric input, proved here for the big fppf site itself: a
morphism from an object with connected underlying scheme into a coproduct of objects of the site
factors through one summand, because the images of the summands are disjoint open sets covering
the coproduct. The summands a connected point misses are then discarded by the observation that
an algebraic space whose sections live only over test schemes with no points admits exactly one
morphism to any algebraic space, the empty sieve being a covering of such a test scheme.

## Main results

* `AlgebraicGeometry.BigFppfOver.isEmpty_toScheme_of_comp_eq_of_ne`: an object of the big fppf
  site mapping to two distinct summands of a coproduct compatibly has no points.
* `AlgebraicGeometry.BigFppfOver.exists_factor_of_isColimit_cofan_of_connectedSpace`: a morphism
  out of an object with connected underlying scheme into a coproduct of the site factors through
  one summand.
* `AlgebraicGeometry.Space.uniqueSectionsOfIsEmpty`,
  `AlgebraicGeometry.Space.homOfEmptySupport` and
  `AlgebraicGeometry.Space.hom_ext_of_emptySupport`: an algebraic space over `B` whose sections
  live only over test schemes with no points has exactly one morphism to any algebraic space
  over `B`.
* `AlgebraicGeometry.Space.exists_section_of_isColimit_cofan_representableOver`: the
  representable algebraic space of a field-valued point is, as a coproduct, concentrated in one
  summand, in the form that the inclusion of that summand has a section.
* `AlgebraicGeometry.Space.exists_factorisation_of_fieldValuedPoint`: a field-valued point
  factors through one member of a family whose fibre products exhaust the point.

## Implementation notes

The coproduct of copies of the test scheme of the point is not built by hand: the big fppf site
over `S` already has countable coproducts, and a colimit cofan in it is already known to be a
cover by pairwise disjoint open subschemes, by
`AlgebraicGeometry.isOpenImmersion_toScheme_map_cofan`,
`AlgebraicGeometry.iUnion_range_toScheme_map_cofan` and
`AlgebraicGeometry.ne_toScheme_map_cofan`. That description is all the geometry the connectedness
argument needs, so no coproduct of schemes is ever formed.

Connectedness enters only through `IsClopen.eq_univ`: the part of the source lying over a fixed
summand is open, and its complement is the union of the parts lying over the other summands,
hence open as well.

## References

* [Stacks Project, Tag 0486](https://stacks.math.columbia.edu/tag/0486)
* [Stacks Project, Tag 048T](https://stacks.math.columbia.edu/tag/048T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

section Site

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {I : Type v}
  {U : I → BigFppfOver C S hS} {V : BigFppfOver C S hS} {j : ∀ i, U i ⟶ V}

/-- An object of the big fppf site over `S` which maps to two distinct summands of a coproduct
compatibly with their inclusions has no points: distinct summands have disjoint images. -/
theorem BigFppfOver.isEmpty_toScheme_of_comp_eq_of_ne (hV : IsColimit (Cofan.mk V j))
    {i i' : I} (hii' : i ≠ i') {Z : BigFppfOver C S hS} (t : Z ⟶ U i) (t' : Z ⟶ U i')
    (h : t ≫ j i = t' ≫ j i') :
    IsEmpty ((BigFppfOver.toScheme C S hS).obj Z) := by
  refine ⟨fun z => ne_toScheme_map_cofan hV hii'
    ((BigFppfOver.toScheme C S hS).map t z)
    ((BigFppfOver.toScheme C S hS).map t' z) ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
    h]

/-- **A connected object of the big fppf site over `S` lies in a single summand of a
coproduct.**

The images of the summands in the underlying scheme of the coproduct are open, they cover it,
and distinct summands have disjoint images; so the part of the source lying over a fixed summand
is clopen, and connectedness makes it everything as soon as it is nonempty. The factorisation is
then the lift of a morphism whose image lies in the image of an open immersion. -/
theorem BigFppfOver.exists_factor_of_isColimit_cofan_of_connectedSpace [Small.{u} I]
    (hV : IsColimit (Cofan.mk V j)) {A : BigFppfOver C S hS}
    [ConnectedSpace ((BigFppfOver.toScheme C S hS).obj A)] (g : A ⟶ V) :
    ∃ i, ∃ l : A ⟶ U i, l ≫ j i = g := by
  classical
  have hoi : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme C S hS).map (j i)) := fun i =>
    isOpenImmersion_toScheme_map_cofan hV i
  have hopen : ∀ i, IsOpen (Set.range ((BigFppfOver.toScheme C S hS).map (j i))) := by
    intro i
    have := hoi i
    have h := ((BigFppfOver.toScheme C S hS).map (j i)).opensRange.isOpen
    rwa [Scheme.Hom.coe_opensRange] at h
  have hmem : ∀ y : (BigFppfOver.toScheme C S hS).obj V,
      ∃ i, y ∈ Set.range ((BigFppfOver.toScheme C S hS).map (j i)) :=
    Set.iUnion_eq_univ_iff.1 (iUnion_range_toScheme_map_cofan hV)
  have hpre : ∀ i, IsOpen ((BigFppfOver.toScheme C S hS).map g ⁻¹'
      Set.range ((BigFppfOver.toScheme C S hS).map (j i))) := fun i =>
    (hopen i).preimage (Scheme.Hom.continuous _)
  obtain ⟨x₀⟩ : Nonempty ((BigFppfOver.toScheme C S hS).obj A) := inferInstance
  obtain ⟨i₀, hi₀⟩ := hmem ((BigFppfOver.toScheme C S hS).map g x₀)
  have hcompl : ((BigFppfOver.toScheme C S hS).map g ⁻¹'
      Set.range ((BigFppfOver.toScheme C S hS).map (j i₀)))ᶜ =
      ⋃ i : {i : I // i ≠ i₀}, (BigFppfOver.toScheme C S hS).map g ⁻¹'
        Set.range ((BigFppfOver.toScheme C S hS).map (j i.1)) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_iUnion, Subtype.exists]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := hmem ((BigFppfOver.toScheme C S hS).map g x)
      exact ⟨i, fun hii₀ => hx (hii₀ ▸ hi), hi⟩
    · rintro ⟨i, hii₀, z, hz⟩ ⟨z', hz'⟩
      exact ne_toScheme_map_cofan hV hii₀ z z' (hz.trans hz'.symm)
  have hclopen : IsClopen ((BigFppfOver.toScheme C S hS).map g ⁻¹'
      Set.range ((BigFppfOver.toScheme C S hS).map (j i₀))) := by
    refine ⟨?_, hpre i₀⟩
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_iUnion fun i => hpre i.1
  refine ⟨i₀, BigFppfOver.exists_factor_of_range_le (j i₀) (hoi i₀) g ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (hclopen.eq_univ ⟨x₀, hi₀⟩).ge (Set.mem_univ x)

end Site

namespace Space

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {B : AlgebraicSpaces site S hS}

/-! ### Algebraic spaces supported on test schemes with no points -/

/-- An algebraic space over `S` has exactly one section over a test scheme with no points: the
empty sieve covers such a test scheme, and an algebraic space is a sheaf. -/
@[instance_reducible]
noncomputable def uniqueSectionsOfIsEmpty (F : AlgebraicSpaces site S hS)
    (T : BigFppfOver site S hS)
    (hT : IsEmpty ((BigFppfOver.toScheme site S hS).obj T)) :
    Unique (F.obj.obj (Opposite.op T)) :=
  Types.isTerminalEquivUnique _
    (Sheaf.isTerminalOfBotCover
      (⟨F.obj, F.property.isSheaf⟩ : Sheaf (BigFppfOver.topology site S hS) (Type u))
      T (BigFppfOver.bot_mem_topology T hT))

/-- The morphism of algebraic spaces over `B` out of an algebraic space all of whose sections
live over test schemes with no points: over each such test scheme the target has exactly one
section, which is where the section of the source is sent. -/
noncomputable def homOfEmptySupport (X Y : Over B)
    (hX : ∀ T : BigFppfOver site S hS, X.left.obj.obj (Opposite.op T) →
      IsEmpty ((BigFppfOver.toScheme site S hS).obj T)) : X ⟶ Y := by
  refine Over.homMk (ObjectProperty.homMk
    { app := fun T => ↾fun x =>
        @default _ (uniqueSectionsOfIsEmpty Y.left T.unop (hX T.unop x)).toInhabited
      naturality := ?_ }) ?_
  · intro T T' g
    ext x
    have := uniqueSectionsOfIsEmpty Y.left T'.unop (hX T'.unop ((X.left.obj.map g) x))
    exact Subsingleton.elim _ _
  · apply ObjectProperty.hom_ext
    ext T x
    have := uniqueSectionsOfIsEmpty B T.unop (hX T.unop x)
    exact Subsingleton.elim _ _

/-- Any two morphisms of algebraic spaces over `B` out of an algebraic space all of whose
sections live over test schemes with no points agree. -/
theorem hom_ext_of_emptySupport {X Y : Over B}
    (hX : ∀ T : BigFppfOver site S hS, X.left.obj.obj (Opposite.op T) →
      IsEmpty ((BigFppfOver.toScheme site S hS).obj T)) (f g : X ⟶ Y) : f = g := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  ext T x
  have := uniqueSectionsOfIsEmpty Y.left T.unop (hX T.unop x)
  exact Subsingleton.elim _ _

/-- If every summand of a coproduct other than `D i₀` is supported on test schemes with no
points, then the inclusion of `D i₀` has a section. -/
theorem exists_section_of_isColimit_cofan_of_emptySupport {I : Type v} {R : Over B}
    {D : I → Over B} (d : ∀ i, D i ⟶ R) (hd : IsColimit (Cofan.mk _ d)) (i₀ : I)
    (hempty : ∀ k, k ≠ i₀ → ∀ Z : BigFppfOver site S hS,
      (D k).left.obj.obj (Opposite.op Z) → IsEmpty ((BigFppfOver.toScheme site S hS).obj Z)) :
    ∃ q : R ⟶ D i₀, q ≫ d i₀ = 𝟙 _ := by
  have key : ∀ k, ∃ q : D k ⟶ D i₀, q ≫ d i₀ = d k := by
    intro k
    obtain rfl | hk := eq_or_ne k i₀
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · exact ⟨homOfEmptySupport (D k) (D i₀) (hempty k hk),
        hom_ext_of_emptySupport (hempty k hk) _ _⟩
  choose e he using key
  refine ⟨hd.desc (Cofan.mk (D i₀) e), hd.hom_ext ?_⟩
  rintro ⟨k⟩
  have hdesc : d k ≫ hd.desc (Cofan.mk (D i₀) e) = e k := hd.fac _ ⟨k⟩
  show d k ≫ hd.desc (Cofan.mk (D i₀) e) ≫ d i₀ = d k ≫ 𝟙 _
  rw [← Category.assoc, hdesc, he, Category.comp_id]

/-! ### Splitting off the summand met by a connected point -/

private theorem exists_representableOver_sections {I : Type v} {A V : BigFppfOver site S hS}
    (b : yoneda.obj A ⟶ B.obj) (v : ∀ _ : I, A ⟶ V) (fold : V ⟶ A)
    (hvfold : ∀ i, v i ≫ fold = 𝟙 A) :
    ∃ (vi : ∀ _ : I, representableOver (B := B) A b ⟶
        representableOver (B := B) V (yoneda.map fold ≫ b))
      (π : representableOver (B := B) V (yoneda.map fold ≫ b) ⟶
        representableOver (B := B) A b),
      (∀ i, vi i ≫ π = 𝟙 _) ∧ (∀ i, (vi i).left.hom = yoneda.map (v i)) ∧
        π.left.hom = yoneda.map fold := by
  refine ⟨fun i => Over.homMk (ObjectProperty.homMk (yoneda.map (v i))) ?_,
    Over.homMk (ObjectProperty.homMk (yoneda.map fold)) ?_, ?_, fun _ => rfl, rfl⟩
  · apply ObjectProperty.hom_ext
    show yoneda.map (v i) ≫ yoneda.map fold ≫ b = b
    rw [← Functor.map_comp_assoc, hvfold, CategoryTheory.Functor.map_id, Category.id_comp]
  · apply ObjectProperty.hom_ext
    rfl
  · intro i
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show yoneda.map (v i) ≫ yoneda.map fold = 𝟙 _
    rw [← Functor.map_comp, hvfold, CategoryTheory.Functor.map_id]

/-- The representable algebraic space of an object of the site with connected underlying scheme,
written as a countable coproduct of algebraic spaces over `B`, is concentrated in one summand.

The proof compares the given decomposition with the coproduct `V` of countably many copies of
the test object inside the site: the summands assemble a morphism to the representable algebraic
space of `V`, which is a section of the codiagonal, hence comes from a morphism into `V` of the
test object itself. Connectedness confines that morphism to one copy, and then every other
summand is supported on test schemes with no points. -/
private theorem exists_section_of_isColimit_cofan_of_connectedSpace {I : Type v} [Small.{u} I]
    [Countable I] {A : BigFppfOver site S hS} (b : yoneda.obj A ⟶ B.obj)
    [ConnectedSpace ((BigFppfOver.toScheme site S hS).obj A)] (D : I → Over B)
    (d : ∀ i, D i ⟶ representableOver (B := B) A b) (hd : IsColimit (Cofan.mk _ d)) :
    ∃ i, ∃ q : representableOver (B := B) A b ⟶ D i, q ≫ d i = 𝟙 _ := by
  classical
  obtain ⟨V, v, hv⟩ : Σ' (V : BigFppfOver site S hS) (v : ∀ _ : I, A ⟶ V),
      IsColimit (Cofan.mk V v) :=
    ⟨∐ fun _ : I => A, Sigma.ι _, coproductIsCoproduct _⟩
  obtain ⟨fold, hvfold⟩ : ∃ fold : V ⟶ A, ∀ i, v i ≫ fold = 𝟙 A :=
    ⟨Cofan.IsColimit.desc hv fun _ => 𝟙 A, fun i => Cofan.IsColimit.fac hv _ i⟩
  obtain ⟨vi, π, hviπ, hvileft, hπleft⟩ := exists_representableOver_sections b v fold hvfold
  obtain ⟨f, hf⟩ : ∃ f : representableOver (B := B) A b ⟶
      representableOver (B := B) V (yoneda.map fold ≫ b), ∀ i, d i ≫ f = d i ≫ vi i :=
    ⟨hd.desc (Cofan.mk _ fun i => d i ≫ vi i), fun i => hd.fac _ ⟨i⟩⟩
  have hfπ : f ≫ π = 𝟙 _ := by
    refine hd.hom_ext fun ⟨i⟩ => ?_
    show d i ≫ f ≫ π = d i ≫ 𝟙 _
    rw [← Category.assoc, hf, Category.assoc, hviπ]
  obtain ⟨f₀, hf₀eq⟩ := yoneda.map_surjective (X := A) (Y := V) f.left.hom
  have hfl : (Over.Hom.left (f ≫ π)).hom
      = 𝟙 ((representableOver (B := B) A b).left.obj) := by
    rw [hfπ, Over.id_left, ObjectProperty.FullSubcategory.id_hom]
  simp only [Over.comp_left, ObjectProperty.FullSubcategory.comp_hom, hπleft] at hfl
  have hf₀ : f₀ ≫ fold = 𝟙 A := by
    apply yoneda.map_injective
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    exact (congrArg (fun w => w ≫ yoneda.map fold) hf₀eq).trans hfl
  obtain ⟨i₀, l, hl⟩ :=
    BigFppfOver.exists_factor_of_isColimit_cofan_of_connectedSpace hv f₀
  have hf₀v : f₀ = v i₀ := by
    have h₁ : l ≫ v i₀ ≫ fold = 𝟙 A := by rw [← Category.assoc, hl, hf₀]
    rw [hvfold, Category.comp_id] at h₁
    rw [← hl, h₁, Category.id_comp]
  have hfv : f = vi i₀ := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    rw [hvileft]
    exact hf₀eq.symm.trans (congrArg yoneda.map hf₀v)
  have hempty : ∀ k, k ≠ i₀ → ∀ Z : BigFppfOver site S hS,
      (D k).left.obj.obj (Opposite.op Z) →
        IsEmpty ((BigFppfOver.toScheme site S hS).obj Z) := by
    intro k hk Z z
    have hkv : d k ≫ vi k = d k ≫ vi i₀ := by rw [← hf, hfv]
    have he : (Over.Hom.left (d k ≫ vi k)).hom = (Over.Hom.left (d k ≫ vi i₀)).hom := by
      rw [hkv]
    simp only [Over.comp_left, ObjectProperty.FullSubcategory.comp_hom, hvileft] at he
    obtain ⟨t, ht⟩ := yoneda.map_surjective (X := Z) (Y := A)
      (yonedaEquiv.symm z ≫ (d k).left.hom)
    refine BigFppfOver.isEmpty_toScheme_of_comp_eq_of_ne hv hk t t ?_
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, ht]
    exact congrArg (fun w => yonedaEquiv.symm z ≫ w) he
  exact ⟨i₀, exists_section_of_isColimit_cofan_of_emptySupport d hd i₀ hempty⟩

/-- **A field-valued point of an algebraic space meets only one summand of a coproduct.**

If the representable algebraic space of a field-valued point `p` of `B` is a countable coproduct
of algebraic spaces `D i` over `B`, then the inclusion of one of the summands has a section. The
spectrum of the field of `p` is connected, which is what forbids the point from being spread
over two summands. -/
theorem exists_section_of_isColimit_cofan_representableOver {I : Type v} [Small.{u} I]
    [Countable I] (p : FieldValuedPoint site S hS B.obj) (D : I → Over B)
    (d : ∀ i, D i ⟶ representableOver (B := B) p.siteObject (yonedaEquiv.symm p.value))
    (hd : IsColimit (Cofan.mk _ d)) :
    ∃ i, ∃ q : representableOver (B := B) p.siteObject (yonedaEquiv.symm p.value) ⟶ D i,
      q ≫ d i = 𝟙 _ :=
  have : ConnectedSpace ((BigFppfOver.toScheme site S hS).obj p.siteObject) :=
    inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of p.carrier)))
  exists_section_of_isColimit_cofan_of_connectedSpace _ D d hd

/-- **A field-valued point of an algebraic space factors through one member of a family.**

Let `r` be a morphism from the representable algebraic space of a field-valued point `p` of `B`
to an algebraic space `V` over `B`, and let `v i : F i ⟶ V` be a countable family whose fibre
products with `r` exhaust the source of `r`. Then `r` factors through one of the `F i`. -/
theorem exists_factorisation_of_fieldValuedPoint {I : Type v} [Small.{u} I] [Countable I]
    (p : FieldValuedPoint site S hS B.obj) (F : I → Over B) (V : Over B) (v : ∀ i, F i ⟶ V)
    (r : representableOver (B := B) p.siteObject (yonedaEquiv.symm p.value) ⟶ V)
    (h : IsColimit (Cofan.mk _ (fun i => pullback.fst r (v i)))) :
    ∃ i, ∃ q : representableOver (B := B) p.siteObject (yonedaEquiv.symm p.value) ⟶ F i,
      q ≫ v i = r := by
  obtain ⟨i, q, hq⟩ := exists_section_of_isColimit_cofan_representableOver p _ _ h
  refine ⟨i, q ≫ pullback.snd r (v i), ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, hq, Category.id_comp]

end Space

end AlgebraicGeometry

end
