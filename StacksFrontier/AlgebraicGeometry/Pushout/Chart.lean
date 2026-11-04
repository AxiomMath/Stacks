module

public import StacksFrontier.AlgebraicGeometry.Pushout.CompatibleAffines
public import StacksFrontier.AlgebraicGeometry.Pushout.ClosedImmersionIntegral
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Pushout.SectionsComparison
public import StacksFrontier.AlgebraicGeometry.Pushout.TopologicalRestriction

/-!
# The affine charts of a pushout along a closed immersion and an integral morphism

Let `i : Z ⟶ X` be a closed immersion and `j : Z ⟶ Y` an integral morphism subject to the
fibrewise condition of [Stacks Project, Tag 0ECI], and let

```
Z --i--> X
|        |
j        a
v        v
Y --b--> P
```

be a pushout square of *locally ringed spaces*.  This file shows that `P` is covered by open
subspaces isomorphic to the affine model `Spec (Γ(Y, V) ×_{Γ(Z, T)} Γ(X, U))` of
[Stacks Project, Tag 0ET0], which is what makes `P` a scheme.

The charts are indexed by the opens `W` of `P` whose two preimages `U = a ⁻¹ W` and `V = b ⁻¹ W`
are affine.  Such a `W` exists around every point: over a point of the image of `Y` the
compatible pair of affine opens is [Stacks Project, Tag 0ECJ], and over a point of `X` outside
the closed image of `i` the pair `(U, ⊥)` works.

## Main definitions

* `Stacks.Pushout.toOpens` restricts the codomain of a continuous map to an open containing its
  image.
* `Stacks.Pushout.lrsToPresheafedSpace` is the underlying presheafed space of a locally ringed
  space, as a functor.

## Main results

* `Stacks.Pushout.isPushout_affineModel_locallyRingedSpace` is [Stacks Project, Tag 0ET0] for
  locally ringed spaces, transported to a span of affine schemes.
* `Stacks.Pushout.exists_opens_isAffineOpen_preimage`: every point of the pushout lies in an
  open whose two preimages are affine.
* `Stacks.Pushout.exists_affineChart_of_isPushout`: over such an open the pushout is the affine
  model, by an open immersion whose image is exactly that open.
* `Stacks.Pushout.isIso_ι_app_of_le`: the inclusion of an open subscheme is an isomorphism on
  sections over any smaller open.

## Implementation notes

Everything is stated for a pushout square of locally ringed spaces given as a hypothesis, never
for the colimit: `AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace` does not preserve
colimits, so the pushout of the span of schemes — which is what Tag 0E25 asserts to exist —
carries no information about the underlying locally ringed spaces.

That the comparison map from the affine model is an isomorphism on the underlying spaces is
`Stacks.Pushout.isPushout_of_isOpenEmbedding` applied with the two legs of the affine model
composed with the comparison; taking those as the restricted square, rather than the
`Stacks.Pushout.restrictOpens` maps of
`Stacks.Pushout.isPushout_restrictOpens`, is what lets the two opens `U` and `V` stay free
variables with their defining equations as hypotheses.  On the structure sheaves the comparison
is `Stacks.Pushout.isIso_app_of_isPushout_comparison`, whose three hypotheses are exactly
`Stacks.Pushout.isIso_ι_app_of_le` for the three open immersions of the span.

## References

* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0ECJ](https://stacks.math.columbia.edu/tag/0ECJ)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Pushout

/-- The inclusion of an open subscheme is an isomorphism on sections over any smaller open. -/
lemma isIso_ι_app_of_le {X : Scheme.{u}} (U V : X.Opens) (hV : V ≤ U) : IsIso (U.ι.app V) := by
  have heq : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, U.opensRange_ι, inf_eq_right.mpr hV]
  rw [Scheme.Opens.ι_app, Subsingleton.elim (homOfLE (show U.ι ''ᵁ (U.ι ⁻¹ᵁ V) ≤ V from heq.le)).op
    (eqToHom (congrArg op heq.symm))]
  exact (X.presheaf.mapIso (eqToIso (congrArg op heq.symm))).isIso_hom

/-- `Spec` of a morphism of rings, read as a morphism of locally ringed spaces, is the image
under `AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace` of the naturality square of
`AlgebraicGeometry.Scheme.isoSpec`. -/
lemma map_isoSpec_hom_naturality {A B : Scheme.{u}} [IsAffine A] [IsAffine B] (f : A ⟶ B) :
    Scheme.forgetToLocallyRingedSpace.map A.isoSpec.hom ≫ Spec.locallyRingedSpaceMap f.appTop =
      Scheme.forgetToLocallyRingedSpace.map f ≫
        Scheme.forgetToLocallyRingedSpace.map B.isoSpec.hom :=
  (Scheme.forgetToLocallyRingedSpace.map_comp _ _).symm.trans
    ((congrArg Scheme.forgetToLocallyRingedSpace.map (Scheme.isoSpec_hom_naturality f)).trans
      (Scheme.forgetToLocallyRingedSpace.map_comp _ _))

/-- **The affine model is a pushout of locally ringed spaces.**  For affine `X`, `Y` and `Z` and
a closed immersion `i : Z ⟶ X`, the square of locally ringed spaces underlying `i`, `j` and the
two canonical maps into the affine model is cocartesian.

This is the only form in which [Stacks Project, Tag 0ET0] can be used by the gluing
construction: `AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace` does not preserve colimits,
so the corresponding square of schemes carries no information one layer down. -/
theorem isPushout_affineModel_locallyRingedSpace {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsAffine X] [IsAffine Y] [IsAffine Z] [IsClosedImmersion i] :
    IsPushout (Scheme.forgetToLocallyRingedSpace.map i) (Scheme.forgetToLocallyRingedSpace.map j)
      (Scheme.forgetToLocallyRingedSpace.map (affineModelInl i j))
      (Scheme.forgetToLocallyRingedSpace.map (affineModelInr i j)) := by
  have H := isPushout_specLocallyRingedSpaceMap_of_isPullback i.appTop j.appTop
    (CommRingCat.ofHom (j.appTop.hom.pullbackFst i.appTop.hom))
    (CommRingCat.ofHom (j.appTop.hom.pullbackSnd i.appTop.hom))
    (isPullback_ofHom_pullback j.appTop.hom i.appTop.hom)
    (surjective_appTop_of_isClosedImmersion i)
  refine H.of_iso' (Scheme.forgetToLocallyRingedSpace.mapIso Z.isoSpec)
    (Scheme.forgetToLocallyRingedSpace.mapIso X.isoSpec)
    (Scheme.forgetToLocallyRingedSpace.mapIso Y.isoSpec) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact map_isoSpec_hom_naturality i
  · exact map_isoSpec_hom_naturality j
  · exact (Scheme.forgetToLocallyRingedSpace.map_comp X.isoSpec.hom
      (Spec.map (CommRingCat.ofHom
        (j.appTop.hom.pullbackSnd i.appTop.hom)))).symm.trans (Category.comp_id _).symm
  · exact (Scheme.forgetToLocallyRingedSpace.map_comp Y.isoSpec.hom
      (Spec.map (CommRingCat.ofHom
        (j.appTop.hom.pullbackFst i.appTop.hom)))).symm.trans (Category.comp_id _).symm

/-! ### Compatible affine opens of the pushout -/

section Chart

variable {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) {P : LocallyRingedSpace.{u}}
  {a : Scheme.forgetToLocallyRingedSpace.obj X ⟶ P}
  {b : Scheme.forgetToLocallyRingedSpace.obj Y ⟶ P}

/-- **A compatible pair of opens spans an open of a pushout of locally ringed spaces.**  This is
`Stacks.Pushout.exists_opens_preimage_eq_of_isPushout_base` with the apex a locally ringed
space rather than a scheme; the proof is the same three topological facts. -/
theorem exists_opens_preimage_eq_of_isPushout_base'
    (hbase : IsPushout (Scheme.forgetToLocallyRingedSpace.map i).base
      (Scheme.forgetToLocallyRingedSpace.map j).base a.base b.base)
    (hi : Function.Injective (Scheme.forgetToLocallyRingedSpace.map i).base)
    (U : X.Opens) (V : Y.Opens) (hUV : i ⁻¹ᵁ U = j ⁻¹ᵁ V) :
    ∃ W : Opens P, (W : Set P) = a.base '' (U : Set X) ∪ b.base '' (V : Set Y) ∧
      (Opens.map a.base).obj W = U ∧ (Opens.map b.base).obj W = V := by
  have hUV' : (Scheme.forgetToLocallyRingedSpace.map i).base ⁻¹' (U : Set X) =
      (Scheme.forgetToLocallyRingedSpace.map j).base ⁻¹' (V : Set Y) :=
    congrArg (fun O : Z.Opens ↦ (O : Set Z)) hUV
  refine ⟨⟨_, isOpen_inl_image_union_inr_image _ _ hi hbase hUV' U.2 V.2⟩, rfl,
    TopologicalSpace.Opens.ext ?_, TopologicalSpace.Opens.ext ?_⟩
  · exact preimage_inl_image_union_inr_image _ _ hi hbase hUV'
  · exact preimage_inr_image_union_inr_image _ _ hi hbase hUV'

/-- **Every point of the pushout lies in an open whose two preimages are affine.**  Over a point
in the image of `Y` this is [Stacks Project, Tag 0ECJ]; over a point of `X` outside the image of
the closed immersion the pair `(U, ⊥)` works, and `AlgebraicGeometry.isAffineOpen_bot` makes the
empty open affine. -/
theorem exists_opens_isAffineOpen_preimage [IsClosedImmersion i] [IsIntegralHom j]
    (hfib : ∀ y : Y, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U)
    (hbase : IsPushout (Scheme.forgetToLocallyRingedSpace.map i).base
      (Scheme.forgetToLocallyRingedSpace.map j).base a.base b.base)
    (p : P) :
    ∃ W : Opens P, p ∈ W ∧ IsAffineOpen ((Opens.map a.base).obj W) ∧
      IsAffineOpen ((Opens.map b.base).obj W) := by
  have hi : Function.Injective (Scheme.forgetToLocallyRingedSpace.map i).base :=
    i.isClosedEmbedding.injective
  -- The case of a point in the image of `Y`.
  have hcaseY : ∀ y : Y, ∃ W : Opens P, b.base y ∈ W ∧
      IsAffineOpen ((Opens.map a.base).obj W) ∧ IsAffineOpen ((Opens.map b.base).obj W) := by
    intro y
    obtain ⟨U, V, hU, hV, hyV, hUV⟩ := exists_affineOpens_preimage_eq i j hfib y
    obtain ⟨W, hWset, hWa, hWb⟩ :=
      exists_opens_preimage_eq_of_isPushout_base' i j hbase hi U V hUV
    refine ⟨W, ?_, hWa ▸ hU, hWb ▸ hV⟩
    change (b.base y : P) ∈ (W : Set P)
    rw [hWset]
    exact Or.inr ⟨y, hyV, rfl⟩
  obtain ⟨s, hs⟩ := (isQuotientMap_sum_of_isPushout _ _ hi hbase).surjective p
  rcases s with x | y
  · by_cases hx : x ∈ Set.range (Scheme.forgetToLocallyRingedSpace.map i).base
    · obtain ⟨z, hz⟩ := hx
      obtain ⟨W, hW, h1, h2⟩ := hcaseY (j z)
      refine ⟨W, ?_, h1, h2⟩
      have hcross : a.base (i z) = b.base (j z) :=
        (ConcreteCategory.comp_apply _ _ z).symm.trans
          ((ConcreteCategory.congr_hom hbase.w z).trans (ConcreteCategory.comp_apply _ _ z))
      have hxz : (a.base x : P) = b.base (j z) := hz ▸ hcross
      subst hs
      change (a.base x : P) ∈ W
      rw [hxz]
      exact hW
    · have hclosed : IsClosed (Set.range (Scheme.forgetToLocallyRingedSpace.map i).base) :=
        i.isClosedEmbedding.isClosed_range
      obtain ⟨U, hU, hxU, hUle⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⟨_, isOpen_compl_iff.mpr hclosed⟩ : X.Opens) from hx)
      have hUV : i ⁻¹ᵁ U = (⊥ : Z.Opens) :=
        TopologicalSpace.Opens.ext (Set.eq_empty_iff_forall_notMem.mpr fun z hz ↦
          (hUle hz : i z ∈ (⟨_, isOpen_compl_iff.mpr hclosed⟩ : X.Opens)) ⟨z, rfl⟩)
      obtain ⟨W, hWset, hWa, hWb⟩ :=
        exists_opens_preimage_eq_of_isPushout_base' i j hbase hi U ⊥
          (hUV.trans (Scheme.Hom.preimage_bot j).symm)
      refine ⟨W, ?_, hWa ▸ hU, hWb ▸ isAffineOpen_bot Y⟩
      subst hs
      change (a.base x : P) ∈ (W : Set P)
      rw [hWset]
      exact Or.inl ⟨x, hxU, rfl⟩
  · obtain ⟨W, hW, h1, h2⟩ := hcaseY y
    exact ⟨W, hs ▸ hW, h1, h2⟩

end Chart


/-- A continuous map whose values all lie in an open, read as a map into that open subspace. -/
def toOpens {A B : TopCat.{u}} (f : A ⟶ B) (T : Opens B) (hf : ∀ x : A, f x ∈ T) :
    A ⟶ (Opens.toTopCat B).obj T :=
  TopCat.ofHom ⟨fun x ↦ ⟨f x, hf x⟩, Continuous.subtype_mk f.hom.continuous _⟩

/-- Restricting the codomain and then including again is the original map. -/
@[simp]
lemma toOpens_comp_inclusion {A B : TopCat.{u}} (f : A ⟶ B) (T : Opens B)
    (hf : ∀ x : A, f x ∈ T) : toOpens f T hf ≫ Opens.inclusion' T = f := rfl

/-- The underlying presheafed space of a locally ringed space, as a functor.  Pushout squares
are transported along it in order to apply
`Stacks.Pushout.isIso_app_of_isPushout_comparison`. -/
noncomputable abbrev lrsToPresheafedSpace :
    LocallyRingedSpace.{u} ⥤ PresheafedSpace CommRingCat.{u} :=
  LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace

/-! ### The affine chart -/

section Chart2

variable {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) {P : LocallyRingedSpace.{u}}
  {a : Scheme.forgetToLocallyRingedSpace.obj X ⟶ P}
  {b : Scheme.forgetToLocallyRingedSpace.obj Y ⟶ P}

/-- **The pushout is the affine model over an open with affine preimages.**  Let `i`, `j`, `a`,
`b` be a pushout square of locally ringed spaces with `i : Z ⟶ X` a closed immersion of schemes
and `j : Z ⟶ Y` integral, and let `W` be an open of the apex whose preimages `U` in `X` and `V`
in `Y` are affine.  Then there is a ring `R` — the fibre product
`Γ(Y, V) ×_{Γ(Z, i ⁻¹ V)} Γ(X, U)` — and an open immersion from `Spec R` onto `W`, compatible
with the two canonical maps of the affine model of [Stacks Project, Tag 0ET0].

The two opens are taken as variables with their defining equations as hypotheses so that the
statement stays legible; the equations are used only to recognise a section over `U` as a
section over `W` pulled back. -/
theorem exists_affineChart_of_isPushout [IsClosedImmersion i] [IsIntegralHom j]
    (h : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map j) a b) (W : Opens P)
    (U : X.Opens) (V : Y.Opens) (hUW : U = (Opens.map a.base).obj W)
    (hVW : V = (Opens.map b.base).obj W)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hTV : i ⁻¹ᵁ U = j ⁻¹ᵁ V) :
    ∃ (R : CommRingCat.{u}) (α : U.toScheme ⟶ Spec R) (β : V.toScheme ⟶ Spec R)
      (g : Scheme.forgetToLocallyRingedSpace.obj (Spec R) ⟶ P),
      IsIntegralHom α ∧ IsClosedImmersion β ∧
      IsPullback (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le) α β ∧
      Scheme.forgetToLocallyRingedSpace.map α ≫ g =
        Scheme.forgetToLocallyRingedSpace.map U.ι ≫ a ∧
      Scheme.forgetToLocallyRingedSpace.map β ≫ g =
        Scheme.forgetToLocallyRingedSpace.map V.ι ≫ b ∧
      LocallyRingedSpace.IsOpenImmersion g ∧ Set.range g.base = (W : Set P) := by
  have hiU : IsClosedImmersion (i ∣_ U) := inferInstance
  have hjV : IsIntegralHom (j.resLE V (i ⁻¹ᵁ U) hTV.le) := by
    rw [Scheme.Hom.resLE_congr j hTV.le rfl hTV (@IsIntegralHom),
      Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have instU : IsAffine U.toScheme := hU
  have instV : IsAffine V.toScheme := hV
  have instT : IsAffine (i ⁻¹ᵁ U).toScheme := hU.preimage i
  have HQ := isPushout_affineModel_locallyRingedSpace (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)
  have hsqI : Scheme.forgetToLocallyRingedSpace.map (i ∣_ U) ≫
        Scheme.forgetToLocallyRingedSpace.map U.ι =
      Scheme.forgetToLocallyRingedSpace.map (i ⁻¹ᵁ U).ι ≫
        Scheme.forgetToLocallyRingedSpace.map i := by
    rw [← Scheme.forgetToLocallyRingedSpace.map_comp,
      ← Scheme.forgetToLocallyRingedSpace.map_comp, morphismRestrict_ι]
  have hsqJ : Scheme.forgetToLocallyRingedSpace.map (j.resLE V (i ⁻¹ᵁ U) hTV.le) ≫
        Scheme.forgetToLocallyRingedSpace.map V.ι =
      Scheme.forgetToLocallyRingedSpace.map (i ⁻¹ᵁ U).ι ≫
        Scheme.forgetToLocallyRingedSpace.map j := by
    rw [← Scheme.forgetToLocallyRingedSpace.map_comp,
      ← Scheme.forgetToLocallyRingedSpace.map_comp, Scheme.Hom.resLE_comp_ι]
  obtain ⟨g, hga, hgb⟩ : ∃ g : Scheme.forgetToLocallyRingedSpace.obj
      (affineModel (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ⟶ P,
      Scheme.forgetToLocallyRingedSpace.map
          (affineModelInl (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ≫ g =
        Scheme.forgetToLocallyRingedSpace.map U.ι ≫ a ∧
      Scheme.forgetToLocallyRingedSpace.map
          (affineModelInr (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ≫ g =
        Scheme.forgetToLocallyRingedSpace.map V.ι ≫ b := by
    refine ⟨HQ.desc _ _ ?_, HQ.inl_desc _ _ _, HQ.inr_desc _ _ _⟩
    rw [← Category.assoc, hsqI, Category.assoc, h.w, ← Category.assoc, ← hsqJ, Category.assoc]
  have hi : Function.Injective (Scheme.forgetToLocallyRingedSpace.map i).base :=
    i.isClosedEmbedding.injective
  have hiU' : Function.Injective (Scheme.forgetToLocallyRingedSpace.map (i ∣_ U)).base :=
    (i ∣_ U).isClosedEmbedding.injective
  have hbaseQ := isPushout_base_of_isPushout HQ
  have hbs : ∀ {A B C D : LocallyRingedSpace.{u}} {f : A ⟶ B} {f' : A ⟶ C} {k : B ⟶ D}
      {k' : C ⟶ D}, f ≫ k = f' ≫ k' → f.base ≫ k.base = f'.base ≫ k'.base := fun h ↦ by
    rw [← LocallyRingedSpace.comp_base, ← LocallyRingedSpace.comp_base, h]
  have hpt : ∀ {A B C D : LocallyRingedSpace.{u}} {f : A ⟶ B} {f' : A ⟶ C} {k : B ⟶ D}
      {k' : C ⟶ D}, f ≫ k = f' ≫ k' → ∀ x, k.base (f.base x) = k'.base (f'.base x) :=
    fun h x ↦ ConcreteCategory.congr_hom (hbs h) x
  have hgW : ∀ q, g.base q ∈ W := by
    intro q
    obtain ⟨s, hs⟩ := (isQuotientMap_sum_of_isPushout _ _ hiU' hbaseQ).surjective q
    rcases s with x | y
    · subst hs
      change g.base ((Scheme.forgetToLocallyRingedSpace.map (affineModelInl _ _)).base x) ∈ W
      rw [hpt hga x]
      exact hUW.le (show ((Scheme.forgetToLocallyRingedSpace.map U.ι).base x) ∈ U from x.2)
    · subst hs
      change g.base ((Scheme.forgetToLocallyRingedSpace.map (affineModelInr _ _)).base y) ∈ W
      rw [hpt hgb y]
      exact hVW.le (show ((Scheme.forgetToLocallyRingedSpace.map V.ι).base y) ∈ V from y.2)
  have hg0 : IsIso (toOpens g.base W hgW) := by
    refine IsPushout.isIso_of_comp_eq hbaseQ ?_ (toOpens g.base W hgW) rfl rfl
    refine isPushout_of_isOpenEmbedding (Scheme.forgetToLocallyRingedSpace.map i).base
      (Scheme.forgetToLocallyRingedSpace.map j).base hi (isPushout_base_of_isPushout h)
      (u := (Scheme.forgetToLocallyRingedSpace.map U.ι).base)
      (v := (Scheme.forgetToLocallyRingedSpace.map V.ι).base) (w := Opens.inclusion' W)
      (t := (Scheme.forgetToLocallyRingedSpace.map (i ⁻¹ᵁ U).ι).base)
      (Opens.isOpenEmbedding U) (Opens.isOpenEmbedding V) (Opens.isOpenEmbedding W)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact hbs hsqI
    · exact hbs hsqJ
    · rw [Category.assoc, toOpens_comp_inclusion]
      exact hbs hga
    · rw [Category.assoc, toOpens_comp_inclusion]
      exact hbs hgb
    · rintro x ⟨p, hp⟩
      exact ⟨⟨x, hUW.ge (show (a.base x : P) ∈ W from hp ▸ p.2)⟩, rfl⟩
    · rintro y ⟨p, hp⟩
      exact ⟨⟨y, hVW.ge (show (b.base y : P) ∈ W from hp ▸ p.2)⟩, rfl⟩
    · rintro z ⟨p, hp⟩
      exact ⟨⟨z, show ((Scheme.forgetToLocallyRingedSpace.map i).base z) ∈ U from hp ▸ p.2⟩, rfl⟩
  have hrange : Set.range g.base = (W : Set P) := by
    have hs : Function.Surjective (toOpens g.base W hgW) :=
      (TopCat.homeoOfIso (@asIso _ _ _ _ _ hg0)).surjective
    refine Set.Subset.antisymm (fun p hp ↦ ?_) (fun p hp ↦ ?_)
    · obtain ⟨q, rfl⟩ := hp
      exact hgW q
    · obtain ⟨q, hq⟩ := hs ⟨p, hp⟩
      exact ⟨q, congrArg Subtype.val hq⟩
  have hbo : Topology.IsOpenEmbedding g.base :=
    (Opens.isOpenEmbedding W).comp
      (TopCat.homeoOfIso (@asIso _ _ _ _ _ hg0)).isOpenEmbedding
  refine ⟨_, affineModelInl _ _, affineModelInr _ _, g, inferInstance,
    inferInstance, isPullback_affineModel _ _, hga, hgb, ⟨hbo, ?_⟩, hrange⟩
  intro S
  have hOW : (hbo.functor.obj S : Opens P) ≤ W := by
    rintro _ ⟨q, -, rfl⟩
    exact hgW q
  have hleU : (Opens.map a.base).obj (hbo.functor.obj S) ≤ U := fun x hx ↦
    hUW.ge (show (a.base x : P) ∈ W from hOW hx)
  have hleV : (Opens.map b.base).obj (hbo.functor.obj S) ≤ V := fun y hy ↦
    hVW.ge (show (b.base y : P) ∈ W from hOW hy)
  have hsq : ∀ {A B C D : LocallyRingedSpace.{u}} {f : A ⟶ B} {f' : A ⟶ C} {k : B ⟶ D}
      {k' : C ⟶ D}, f ≫ k = f' ≫ k' →
      lrsToPresheafedSpace.map f ≫ lrsToPresheafedSpace.map k =
        lrsToPresheafedSpace.map f' ≫ lrsToPresheafedSpace.map k' := fun h ↦ by
    rw [← lrsToPresheafedSpace.map_comp, ← lrsToPresheafedSpace.map_comp, h]
  exact isIso_app_of_isPushout_comparison (h.map lrsToPresheafedSpace)
    (HQ.map lrsToPresheafedSpace) (hsq hga) (hsq hgb) (hsq hsqI) (hsq hsqJ) (hbo.functor.obj S)
    (isIso_ι_app_of_le U _ hleU) (isIso_ι_app_of_le V _ hleV)
    (isIso_ι_app_of_le (i ⁻¹ᵁ U) _ (i.preimage_mono hleU))

end Chart2

end Stacks.Pushout

end
