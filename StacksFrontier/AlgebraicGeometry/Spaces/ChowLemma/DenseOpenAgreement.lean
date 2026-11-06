module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.OpenFamilyGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SchemeImageDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparatedEqualizer

/-!
# Agreement of the restrictions of the cover of Stacks 089J on a dense open

Let `Z` be an object of the big fppf category over `S`, let `gᵢ : Z ⟶ Y` be `d` morphisms of
schemes and let `W ⊆ Y` be open, so that the opens `gᵢ⁻¹(W)` cover
`X' = AlgebraicGeometry.Space.unionPreimageObj`. Morphisms `gᵢ⁻¹(W) ⟶ X` into an algebraic space
`X` separated over the base which agree on a scheme-theoretically dense quasi-compact open
`V ⊆ Z` lying inside every `gᵢ⁻¹(W)` agree on every common refinement, and so glue to a unique
morphism `X' ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.openSubObjLift`: a morphism of the site whose range lies in an open of
  its target, factored through that open.
* `AlgebraicGeometry.Space.preimageObjι`, `AlgebraicGeometry.Space.unionPreimageObjι`: the
  inclusions of a member `gᵢ⁻¹(W)` of the covering and of `X'` itself into `Z`.
* `AlgebraicGeometry.Space.overlapObj`: the overlap `gᵢ⁻¹(W) ⊓ gᵢ'⁻¹(W)` of two members of the
  covering, as an object of the big fppf category over `S`, with its inclusion
  `AlgebraicGeometry.Space.overlapObjι` into `Z` and its two open immersions
  `AlgebraicGeometry.Space.overlapInclLeft` and `AlgebraicGeometry.Space.overlapInclRight` into
  those members.

## Main results

* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_yoneda_eq_top_of_comp`: scheme-theoretic
  density of a quasi-compact morphism of the site restricts to an open of the site through which
  it factors.
* `AlgebraicGeometry.Space.exists_factor_overlapObj`: a pair of morphisms into two members of the
  covering which agree in `Z` factors through their overlap.
* `AlgebraicGeometry.Space.eq_comp_overlapIncl_of_eq_on_dense`: two of the `d` morphisms,
  restricted to the overlap of their domains, agree as soon as they agree on a
  scheme-theoretically dense open of `Z` lying inside both domains and the target is separated
  over the base.
* `AlgebraicGeometry.Space.agree_unionPreimageIncl_of_eq_on_dense`: under the same hypotheses
  the `d` morphisms agree on every common refinement of their domains.
* `AlgebraicGeometry.Space.existsUnique_glueHom_unionPreimageObj_of_eq_on_dense`: **the morphism
  `X' ⟶ X` of Stacks 089J exists and is unique**, given the `d` morphisms, a dense open inside
  all of their domains on which they agree, and separatedness of `X` over the base.
* `AlgebraicGeometry.Space.existsUnique_glueHom_unionPreimageObj_of_eq_on_dominant`: the same,
  with the density hypothesis in its scheme-level form.

## References

* [Stacks Project, Tag 084N](https://stacks.math.columbia.edu/tag/084N)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Restriction of scheme-theoretic density to an open of the site -/

/-- **A morphism of the big fppf category over `S` which becomes a monomorphism of schemes is a
monomorphism.** -/
theorem mono_of_mono_map_toScheme {A D : BigFppfOver B S hS} (j : A ⟶ D)
    (hj : Mono ((BigFppfOver.toScheme B S hS).map j)) : Mono j :=
  ⟨fun {_} g₁ g₂ h => BigFppfOver.map_toScheme_injective B S hS
    ((cancel_mono ((BigFppfOver.toScheme B S hS).map j)).1 (by
      rw [← Functor.map_comp, ← Functor.map_comp, h]))⟩

/-- **A square whose top edge is an identity and whose right edge is a monomorphism is
cartesian.** -/
theorem isPullback_id_comp_of_mono {C : Type*} [Category C] {V O D : C} (v : V ⟶ O) (j : O ⟶ D)
    [Mono j] : IsPullback (𝟙 V) v (v ≫ j) j := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp) (fun s => s.fst) (fun s => ?_)
    (fun s => ?_) (fun s m h₁ _ => ?_))
  · simp
  · exact (cancel_mono j).1 (by simpa using s.condition)
  · simpa using h₁

/-- **Scheme-theoretic density restricts to an open of the site.** If a quasi-compact morphism
`v ≫ j` of the big fppf category over `S` has scheme-theoretically dense image and `j` is an open
immersion of schemes, then `v` has scheme-theoretically dense image too. -/
theorem schemeTheoreticImageSubfunctor_yoneda_eq_top_of_comp {V O D : BigFppfOver B S hS}
    (v : V ⟶ O) (j : O ⟶ D)
    [hji : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map (v ≫ j))]
    (hdense : schemeTheoreticImageSubfunctor B S hS (yoneda.map (v ≫ j)) = ⊤) :
    schemeTheoreticImageSubfunctor B S hS (yoneda.map v) = ⊤ := by
  have hmono : Mono j := mono_of_mono_map_toScheme B S hS j inferInstance
  have hsq : IsPullback (𝟙 V) v (v ≫ j) j := isPullback_id_comp_of_mono v j
  have hpb : IsPullback (pullback.fst (v ≫ j) j) (pullback.snd (v ≫ j) j) (v ≫ j) j :=
    IsPullback.of_hasPullback (v ≫ j) j
  have he : (hpb.isoIsPullback V O hsq).hom ≫ v = pullback.snd (v ≫ j) j :=
    IsPullback.isoIsPullback_hom_snd V O hpb hsq
  have hiso : IsIso (yoneda.map (hpb.isoIsPullback V O hsq).hom) := inferInstance
  have hepi : Epi (yoneda.map (hpb.isoIsPullback V O hsq).hom) := IsIso.epi_of_iso _
  have hrange : Subfunctor.range (yoneda.map (pullback.snd (v ≫ j) j)) =
      Subfunctor.range (yoneda.map v) := by
    rw [← he, Functor.map_comp, Subfunctor.range_comp,
      @Subfunctor.range_eq_top _ _ _ _ (yoneda.map (hpb.isoIsPullback V O hsq).hom) hepi,
      Subfunctor.image_top]
  have h089E := schemeTheoreticImageSubfunctor_pullback_snd_yoneda_of_flat B S hS j (v ≫ j)
  rw [hdense] at h089E
  rw [schemeTheoreticImageSubfunctor_congr_range' B S hS (yoneda.map v)
      (yoneda.map (pullback.snd (v ≫ j) j)) (isAlgebraicSpace_yoneda B S hS O) hrange.symm,
    h089E]
  exact (Subfunctor.preimage_eq_top_iff ⊤ (yoneda.map j)).2 le_top

/-! ### Lifting a morphism into an open of the site -/

/-- The range of a composite of morphisms of schemes lies in the range of its second factor. -/
theorem range_base_comp_subset {A D C : Scheme.{u}} (f : A ⟶ D) (h : D ⟶ C) :
    Set.range ⇑(f ≫ h) ⊆ Set.range ⇑h := by
  rintro x ⟨y, rfl⟩
  exact ⟨f.base y, by simp⟩

/-- **A morphism of the big fppf category over `S` whose range lies in an open of the target
factors through that open**, as a morphism of the site. -/
def openSubObjLift (T : BigFppfOver B S hS) (U : T.left.obj.Opens) {A : BigFppfOver B S hS}
    (a : A ⟶ T) (ha : Set.range ⇑((BigFppfOver.toScheme B S hS).map a) ⊆ (U : Set T.left.obj)) :
    A ⟶ BigFppfOver.openSubObj B S hS T U :=
  Over.homMk
    (ObjectProperty.homMk
      (Y := B.obj (BigFppfOver.contains_opens B T.left.property U))
      (IsOpenImmersion.lift U.ι ((BigFppfOver.toScheme B S hS).map a) (by rwa [U.range_ι])))
    (by
      apply ObjectProperty.hom_ext
      rw [ObjectProperty.FullSubcategory.comp_hom]
      change IsOpenImmersion.lift U.ι ((BigFppfOver.toScheme B S hS).map a) _ ≫ U.ι ≫ T.hom.hom
        = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac,
        show (BigFppfOver.toScheme B S hS).map a = B.inclusion.map a.left from rfl,
        show (Over.hom T).hom = B.inclusion.map T.hom from rfl,
        show (Over.hom A).hom = B.inclusion.map A.hom from rfl, ← Functor.map_comp, Over.w])

/-- The scheme morphism underlying `AlgebraicGeometry.Space.openSubObjLift`, followed by the
inclusion of the open, is the scheme morphism underlying the original morphism. -/
theorem openSubObjLift_toScheme_comp (T : BigFppfOver B S hS) (U : T.left.obj.Opens)
    {A : BigFppfOver B S hS} (a : A ⟶ T)
    (ha : Set.range ⇑((BigFppfOver.toScheme B S hS).map a) ⊆ (U : Set T.left.obj)) :
    (BigFppfOver.toScheme B S hS).map (openSubObjLift B S hS T U a ha) ≫ U.ι =
      (BigFppfOver.toScheme B S hS).map a :=
  IsOpenImmersion.lift_fac _ _ _

/-- The scheme morphism underlying the inclusion of an open `U` of the site is the inclusion
`U.ι` of the open subscheme. -/
theorem openSubHom_toScheme (T : BigFppfOver B S hS) (U : T.left.obj.Opens) :
    (BigFppfOver.toScheme B S hS).map (BigFppfOver.openSubHom B S hS T U) = U.ι :=
  rfl

/-- **The inclusion of an open of the site is a monomorphism.** -/
theorem mono_openSubHom (T : BigFppfOver B S hS) (U : T.left.obj.Opens) :
    Mono (BigFppfOver.openSubHom B S hS T U) :=
  mono_of_mono_map_toScheme B S hS _ (by rw [openSubHom_toScheme]; infer_instance)

/-- `AlgebraicGeometry.Space.openSubObjLift`, followed by the inclusion of the open, is the
original morphism. -/
theorem openSubObjLift_comp_openSubHom (T : BigFppfOver B S hS) (U : T.left.obj.Opens)
    {A : BigFppfOver B S hS} (a : A ⟶ T)
    (ha : Set.range ⇑((BigFppfOver.toScheme B S hS).map a) ⊆ (U : Set T.left.obj)) :
    openSubObjLift B S hS T U a ha ≫ BigFppfOver.openSubHom B S hS T U = a :=
  BigFppfOver.map_toScheme_injective B S hS
    (show (BigFppfOver.toScheme B S hS).map (openSubObjLift B S hS T U a ha ≫
        BigFppfOver.openSubHom B S hS T U) = (BigFppfOver.toScheme B S hS).map a by
      rw [Functor.map_comp, openSubHom_toScheme, openSubObjLift_toScheme_comp])

/-! ### The overlap of two members of the covering of `X'` -/

section UnionPreimage

variable (Z : BigFppfOver B S hS) {Y : Scheme.{u}} {n : ℕ}
    (g : Fin n → (Z.left.obj ⟶ Y)) (W : Y.Opens)

/-- The inclusion of the `i`-th member `gᵢ⁻¹(W)` of the covering into `Z`. -/
def preimageObjι (i : Fin n) : preimageObj B S hS Z g W i ⟶ Z :=
  BigFppfOver.openSubHom B S hS Z (g i ⁻¹ᵁ W)

/-- The scheme morphism underlying `AlgebraicGeometry.Space.preimageObjι` is the inclusion of the
open subscheme `gᵢ⁻¹(W)`. -/
theorem preimageObjι_toScheme (i : Fin n) :
    (BigFppfOver.toScheme B S hS).map (preimageObjι B S hS Z g W i) = (g i ⁻¹ᵁ W).ι :=
  rfl

/-- The inclusion of a member of the covering into `Z` is a monomorphism. -/
theorem mono_preimageObjι (i : Fin n) : Mono (preimageObjι B S hS Z g W i) :=
  mono_openSubHom B S hS Z (g i ⁻¹ᵁ W)

/-- The inclusion of `X' = ⋃ᵢ gᵢ⁻¹(W)` into `Z`. -/
def unionPreimageObjι : unionPreimageObj B S hS Z g W ⟶ Z :=
  BigFppfOver.openSubHom B S hS Z (unionPreimageOpens B S hS Z g W)

/-- The scheme morphism underlying `AlgebraicGeometry.Space.unionPreimageObjι` is the inclusion
of the open subscheme `X'`. -/
theorem unionPreimageObjι_toScheme :
    (BigFppfOver.toScheme B S hS).map (unionPreimageObjι B S hS Z g W) =
      (unionPreimageOpens B S hS Z g W).ι :=
  rfl

/-- The inclusion of `gᵢ⁻¹(W)` into `X'`, followed by the inclusion of `X'` into `Z`, is the
inclusion of `gᵢ⁻¹(W)` into `Z`. -/
theorem unionPreimageIncl_comp_unionPreimageObjι (i : Fin n) :
    unionPreimageIncl B S hS Z g W i ≫ unionPreimageObjι B S hS Z g W =
      preimageObjι B S hS Z g W i :=
  BigFppfOver.map_toScheme_injective B S hS
    (show (BigFppfOver.toScheme B S hS).map
        (unionPreimageIncl B S hS Z g W i ≫ unionPreimageObjι B S hS Z g W) =
      (BigFppfOver.toScheme B S hS).map (preimageObjι B S hS Z g W i) by
      rw [Functor.map_comp, unionPreimageIncl_toScheme, unionPreimageObjι_toScheme,
        preimageObjι_toScheme]
      exact Scheme.homOfLE_ι _ _)

/-- **The overlap `gᵢ⁻¹(W) ⊓ gᵢ'⁻¹(W)` of two members of the covering of `X'`**, as an object of
the big fppf category over `S`. -/
abbrev overlapObj (i i' : Fin n) : BigFppfOver B S hS :=
  BigFppfOver.openSubObj B S hS Z (g i ⁻¹ᵁ W ⊓ g i' ⁻¹ᵁ W)

/-- The inclusion of the overlap of two members of the covering into `Z`. -/
def overlapObjι (i i' : Fin n) : overlapObj B S hS Z g W i i' ⟶ Z :=
  BigFppfOver.openSubHom B S hS Z (g i ⁻¹ᵁ W ⊓ g i' ⁻¹ᵁ W)

/-- The scheme morphism underlying `AlgebraicGeometry.Space.overlapObjι` is the inclusion of the
open subscheme `gᵢ⁻¹(W) ⊓ gᵢ'⁻¹(W)`. -/
theorem overlapObjι_toScheme (i i' : Fin n) :
    (BigFppfOver.toScheme B S hS).map (overlapObjι B S hS Z g W i i') =
      (g i ⁻¹ᵁ W ⊓ g i' ⁻¹ᵁ W).ι :=
  rfl

/-- The inclusion of the overlap into the `i`-th member of the covering. -/
def overlapInclLeft (i i' : Fin n) :
    overlapObj B S hS Z g W i i' ⟶ preimageObj B S hS Z g W i :=
  openSubObjLift B S hS Z (g i ⁻¹ᵁ W) (overlapObjι B S hS Z g W i i')
    (by rw [overlapObjι_toScheme, Scheme.Opens.range_ι]; exact fun _ hx => hx.1)

/-- The inclusion of the overlap into the `i'`-th member of the covering. -/
def overlapInclRight (i i' : Fin n) :
    overlapObj B S hS Z g W i i' ⟶ preimageObj B S hS Z g W i' :=
  openSubObjLift B S hS Z (g i' ⁻¹ᵁ W) (overlapObjι B S hS Z g W i i')
    (by rw [overlapObjι_toScheme, Scheme.Opens.range_ι]; exact fun _ hx => hx.2)

/-- The inclusion of the overlap into the `i`-th member of the covering, followed by the inclusion
of that member into `Z`, is the inclusion of the overlap into `Z`. -/
theorem overlapInclLeft_comp_preimageObjι (i i' : Fin n) :
    overlapInclLeft B S hS Z g W i i' ≫ preimageObjι B S hS Z g W i =
      overlapObjι B S hS Z g W i i' :=
  openSubObjLift_comp_openSubHom B S hS Z _ _ _

/-- The inclusion of the overlap into the `i'`-th member of the covering, followed by the
inclusion of that member into `Z`, is the inclusion of the overlap into `Z`. -/
theorem overlapInclRight_comp_preimageObjι (i i' : Fin n) :
    overlapInclRight B S hS Z g W i i' ≫ preimageObjι B S hS Z g W i' =
      overlapObjι B S hS Z g W i i' :=
  openSubObjLift_comp_openSubHom B S hS Z _ _ _

/-- **A pair of morphisms into two members of the covering which agree in `Z` factors through
their overlap.** -/
theorem exists_factor_overlapObj {T : BigFppfOver B S hS} (i i' : Fin n)
    (a : T ⟶ preimageObj B S hS Z g W i) (a' : T ⟶ preimageObj B S hS Z g W i')
    (h : a ≫ preimageObjι B S hS Z g W i = a' ≫ preimageObjι B S hS Z g W i') :
    ∃ b : T ⟶ overlapObj B S hS Z g W i i',
      b ≫ overlapInclLeft B S hS Z g W i i' = a ∧
        b ≫ overlapInclRight B S hS Z g W i i' = a' := by
  have hr : Set.range ⇑((BigFppfOver.toScheme B S hS).map
      (a ≫ preimageObjι B S hS Z g W i)) ⊆
      ((g i ⁻¹ᵁ W ⊓ g i' ⁻¹ᵁ W : Z.left.obj.Opens) : Set Z.left.obj) := by
    refine Set.subset_inter ?_ ?_
    · rw [Functor.map_comp, preimageObjι_toScheme]
      exact (range_base_comp_subset _ _).trans (Scheme.Opens.range_ι _).subset
    · rw [h, Functor.map_comp, preimageObjι_toScheme]
      exact (range_base_comp_subset _ _).trans (Scheme.Opens.range_ι _).subset
  have hb : openSubObjLift B S hS Z (g i ⁻¹ᵁ W ⊓ g i' ⁻¹ᵁ W)
      (a ≫ preimageObjι B S hS Z g W i) hr ≫ overlapObjι B S hS Z g W i i' =
      a ≫ preimageObjι B S hS Z g W i :=
    openSubObjLift_comp_openSubHom B S hS Z _ _ hr
  refine ⟨openSubObjLift B S hS Z _ _ hr, ?_, ?_⟩
  · have := mono_preimageObjι B S hS Z g W i
    refine (cancel_mono (preimageObjι B S hS Z g W i)).1 ?_
    rw [Category.assoc, overlapInclLeft_comp_preimageObjι, hb]
  · have := mono_preimageObjι B S hS Z g W i'
    refine (cancel_mono (preimageObjι B S hS Z g W i')).1 ?_
    rw [Category.assoc, overlapInclRight_comp_preimageObjι, hb, h]

/-! ### The agreement step, and the morphism `X' ⟶ X` -/

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `X` be an algebraic space over `S` whose structure
morphism `q` is separated, let `v : V ⟶ Z` be a quasi-compact open immersion of the site with
scheme-theoretically dense image which factors through every member `gᵢ⁻¹(W)` of the covering of
`X'`, and let `φ i : gᵢ⁻¹(W) ⟶ X` be morphisms which agree after restriction to `V`. Then any two
of them agree on the overlap of their domains. -/
theorem eq_comp_overlapIncl_of_eq_on_dense (hX : IsAlgebraicSpace B S hS X)
    (q : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) (hq : IsSeparated B S hS q)
    {V : BigFppfOver B S hS} (v : V ⟶ Z)
    (hvo : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v))
    (hvq : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map v))
    (hvdense : schemeTheoreticImageSubfunctor B S hS (yoneda.map v) = ⊤)
    (vp : ∀ i, V ⟶ preimageObj B S hS Z g W i)
    (hvp : ∀ i, vp i ≫ preimageObjι B S hS Z g W i = v)
    (φ : ∀ i, (yoneda.obj (preimageObj B S hS Z g W i) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ X)
    (hagree : ∀ i i', yoneda.map (vp i) ≫ φ i = yoneda.map (vp i') ≫ φ i') (i i' : Fin n) :
    yoneda.map (overlapInclLeft B S hS Z g W i i') ≫ φ i =
      yoneda.map (overlapInclRight B S hS Z g W i i') ≫ φ i' := by
  obtain ⟨vo, hvoL, hvoR⟩ := exists_factor_overlapObj B S hS Z g W i i' (vp i) (vp i')
    (by rw [hvp i, hvp i'])
  have hvoZ : vo ≫ overlapObjι B S hS Z g W i i' = v := by
    rw [← overlapInclLeft_comp_preimageObjι B S hS Z g W i i', ← Category.assoc, hvoL, hvp i]
  have : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (overlapObjι B S hS Z g W i i')) := by
    rw [overlapObjι_toScheme]; infer_instance
  have : AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map (vo ≫ overlapObjι B S hS Z g W i i')) := by
    rw [hvoZ]; exact hvq
  have hvodense : schemeTheoreticImageSubfunctor B S hS (yoneda.map vo) = ⊤ :=
    schemeTheoreticImageSubfunctor_yoneda_eq_top_of_comp B S hS vo
      (overlapObjι B S hS Z g W i i') (by rw [hvoZ]; exact hvdense)
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map vo) := by
    have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map vo ≫
        (BigFppfOver.toScheme B S hS).map (overlapObjι B S hS Z g W i i')) := by
      rw [← Functor.map_comp, hvoZ]; exact hvo
    exact IsOpenImmersion.of_comp _
      ((BigFppfOver.toScheme B S hS).map (overlapObjι B S hS Z g W i i'))
  refine eq_of_eq_on_of_schemeTheoreticImageSubfunctor_eq_top B S hS
    (isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS))))
    (isAlgebraicSpace_yoneda B S hS (overlapObj B S hS Z g W i i')) hX
    ((yoneda.map (overlapInclLeft B S hS Z g W i i') ≫ φ i) ≫ q) q _ _ rfl
    ((isTerminal_yoneda_obj_base B S hS).hom_ext _ _) (Subfunctor.range (yoneda.map vo))
    (isOpenSubspace_range_of_isOpenImmersion V (yoneda.map vo)
      (isOpenImmersion_yoneda_map B S hS vo inferInstance)) ?_ ?_ hq
  · refine (cancel_epi (Subfunctor.toRange (yoneda.map vo))).1 ?_
    simp only [← Category.assoc, Subfunctor.toRange_ι, ← Functor.map_comp, hvoL, hvoR]
    exact hagree i i'
  · rw [schemeTheoreticImageSubfunctor_congr_range' B S hS
      (Subfunctor.range (yoneda.map vo)).ι (yoneda.map vo)
      (isAlgebraicSpace_yoneda B S hS (overlapObj B S hS Z g W i i'))
      (by rw [Subfunctor.range_ι])]
    exact hvodense

/-- Under the hypotheses of `AlgebraicGeometry.Space.eq_comp_overlapIncl_of_eq_on_dense`, any two
of the morphisms `φ i` agree on every common refinement of their domains over `X'`. -/
theorem agree_unionPreimageIncl_of_eq_on_dense (hX : IsAlgebraicSpace B S hS X)
    (q : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) (hq : IsSeparated B S hS q)
    {V : BigFppfOver B S hS} (v : V ⟶ Z)
    (hvo : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v))
    (hvq : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map v))
    (hvdense : schemeTheoreticImageSubfunctor B S hS (yoneda.map v) = ⊤)
    (vp : ∀ i, V ⟶ preimageObj B S hS Z g W i)
    (hvp : ∀ i, vp i ≫ preimageObjι B S hS Z g W i = v)
    (φ : ∀ i, (yoneda.obj (preimageObj B S hS Z g W i) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ X)
    (hagree : ∀ i i', yoneda.map (vp i) ≫ φ i = yoneda.map (vp i') ≫ φ i')
    (T : BigFppfOver B S hS) (i i' : Fin n) (a : T ⟶ preimageObj B S hS Z g W i)
    (a' : T ⟶ preimageObj B S hS Z g W i')
    (hcomp : a ≫ unionPreimageIncl B S hS Z g W i =
      a' ≫ unionPreimageIncl B S hS Z g W i') :
    yoneda.map a ≫ φ i = yoneda.map a' ≫ φ i' := by
  have hZ : a ≫ preimageObjι B S hS Z g W i = a' ≫ preimageObjι B S hS Z g W i' := by
    rw [← unionPreimageIncl_comp_unionPreimageObjι B S hS Z g W i,
      ← unionPreimageIncl_comp_unionPreimageObjι B S hS Z g W i', ← Category.assoc,
      ← Category.assoc, hcomp]
  obtain ⟨b, hbL, hbR⟩ := exists_factor_overlapObj B S hS Z g W i i' a a' hZ
  calc yoneda.map a ≫ φ i
      = yoneda.map b ≫ yoneda.map (overlapInclLeft B S hS Z g W i i') ≫ φ i := by
        rw [← hbL, Functor.map_comp, Category.assoc]
    _ = yoneda.map b ≫ yoneda.map (overlapInclRight B S hS Z g W i i') ≫ φ i' := by
        rw [eq_comp_overlapIncl_of_eq_on_dense B S hS Z g W hX q hq v hvo hvq hvdense vp hvp φ
          hagree i i']
    _ = yoneda.map a' ≫ φ i' := by rw [← hbR, Functor.map_comp, Category.assoc]

/-- **The morphism `X' ⟶ X` of Stacks 089J exists and is unique.** Let `X` be an algebraic space
separated over the base, let `v : V ⟶ Z` be a quasi-compact open immersion with
scheme-theoretically dense image factoring through each `gᵢ⁻¹(W)`, and let
`φ i : gᵢ⁻¹(W) ⟶ X` be morphisms which agree after restriction to `V`. Then there is a unique
morphism out of `AlgebraicGeometry.Space.unionPreimageObj` restricting to every `φ i`. -/
theorem existsUnique_glueHom_unionPreimageObj_of_eq_on_dense (hX : IsAlgebraicSpace B S hS X)
    (q : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) (hq : IsSeparated B S hS q)
    {V : BigFppfOver B S hS} (v : V ⟶ Z)
    (hvo : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v))
    (hvq : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map v))
    (hvdense : schemeTheoreticImageSubfunctor B S hS (yoneda.map v) = ⊤)
    (vp : ∀ i, V ⟶ preimageObj B S hS Z g W i)
    (hvp : ∀ i, vp i ≫ preimageObjι B S hS Z g W i = v)
    (φ : ∀ i, (yoneda.obj (preimageObj B S hS Z g W i) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ X)
    (hagree : ∀ i i', yoneda.map (vp i) ≫ φ i = yoneda.map (vp i') ≫ φ i') :
    ∃! ψ : (yoneda.obj (unionPreimageObj B S hS Z g W) :
        (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ X,
      ∀ i, yoneda.map (unionPreimageIncl B S hS Z g W i) ≫ ψ = φ i := by
  obtain ⟨ψ, hψ, huniq⟩ := glueHom_unionPreimageObj B S hS Z g W hX (fun i => φ i.down)
    (fun T i i' a a' hc => agree_unionPreimageIncl_of_eq_on_dense B S hS Z g W hX q hq v hvo
      hvq hvdense vp hvp φ hagree T i.down i'.down a a' hc)
  exact ⟨ψ, fun i => hψ ⟨i⟩, fun ψ' hψ' => huniq ψ' fun i => hψ' i.down⟩

/-- **The morphism `X' ⟶ X` of Stacks 089J, with the density hypothesis in scheme-level form.**
The statement of
`AlgebraicGeometry.Space.existsUnique_glueHom_unionPreimageObj_of_eq_on_dense`, with `v`
scheme-theoretically dominant as a morphism of schemes. -/
theorem existsUnique_glueHom_unionPreimageObj_of_eq_on_dominant (hX : IsAlgebraicSpace B S hS X)
    (q : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) (hq : IsSeparated B S hS q)
    {V : BigFppfOver B S hS} (v : V ⟶ Z)
    (hvo : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v))
    (hvq : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map v))
    (hvdom : IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map v))
    (vp : ∀ i, V ⟶ preimageObj B S hS Z g W i)
    (hvp : ∀ i, vp i ≫ preimageObjι B S hS Z g W i = v)
    (φ : ∀ i, (yoneda.obj (preimageObj B S hS Z g W i) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ X)
    (hagree : ∀ i i', yoneda.map (vp i) ≫ φ i = yoneda.map (vp i') ≫ φ i') :
    ∃! ψ : (yoneda.obj (unionPreimageObj B S hS Z g W) :
        (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ X,
      ∀ i, yoneda.map (unionPreimageIncl B S hS Z g W i) ≫ ψ = φ i :=
  existsUnique_glueHom_unionPreimageObj_of_eq_on_dense B S hS Z g W hX q hq v hvo hvq
    (schemeTheoreticImageSubfunctor_eq_top_of_isSchemeTheoreticallyDominant B S hS v hvdom)
    vp hvp φ hagree

end UnionPreimage

end AlgebraicGeometry.Space

end
