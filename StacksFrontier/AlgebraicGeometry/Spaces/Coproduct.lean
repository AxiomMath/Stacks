module

public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Coproducts in the big fppf site

A colimit cofan in the big fppf site `AlgebraicGeometry.BigFppfOver` over a scheme `S` is a
covering of its vertex by pairwise disjoint open subschemes, the images of its members; for a
small index type it is therefore a coproduct in the category of all schemes.

## Main definitions

* `AlgebraicGeometry.cofanSel` is the morphism `V ⟶ V ⨿ V` separating one member of a
  colimit cofan from all the others. Its two fibres are the complementary open subschemes
  of `V` through which the member and its complement factor.

## Main results

* `AlgebraicGeometry.isOpenImmersion_toScheme_map_cofan`: every member of a colimit cofan
  in the big fppf site over `S` is an open immersion on underlying schemes.
* `AlgebraicGeometry.ne_toScheme_map_cofan`: distinct members have disjoint images.
* `AlgebraicGeometry.iUnion_range_toScheme_map_cofan`: the members cover the vertex.
* `AlgebraicGeometry.nonempty_isColimit_cofan_toScheme`: consequently, for a small index
  type a colimit cofan of the big fppf site over `S` is a colimit cofan of schemes.
* `AlgebraicGeometry.exists_restrict_bigFppfOver`: an open subscheme of an object of the
  big fppf site over `S` is again an object of that site, with the expected universal
  property.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v

namespace AlgebraicGeometry

variable {κ : Cardinal.{u}}

/-- Schemes of size below a cutoff are closed under at most countable coproducts. -/
lemma schemeSizeBelow_isClosedUnderColimitsOfShape_discrete (hκ : ℵ₀ < κ)
    (hcof : ℵ₀ < κ.ord.cof) {ι : Type u} (hι : #ι ≤ ℵ₀) :
    (schemeSizeBelow κ).IsClosedUnderColimitsOfShape (Discrete ι) := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  intro X hX
  rcases hX with ⟨F, hF⟩
  show (colimit F).size < κ
  rw [Scheme.size_congr (HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := F)))]
  exact Scheme.size_sigmaObj_lt hκ hcof hι _ fun i => hF ⟨i⟩

/-- The objects of a big fppf site are closed under binary coproducts. -/
instance schemeSizeBelow_isClosedUnderColimitsOfShape_walkingPair (B : BigFppfSite.{u}) :
    (schemeSizeBelow B.cutoff).IsClosedUnderColimitsOfShape (Discrete WalkingPair) :=
  haveI := schemeSizeBelow_isClosedUnderColimitsOfShape_discrete
    B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
    (ι := ULift.{u} WalkingPair) (by simp)
  ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
    (Discrete.equivalence Equiv.ulift)

/-- The objects of a big fppf site are closed under the empty coproduct, that is, they
contain an initial object. -/
instance schemeSizeBelow_isClosedUnderColimitsOfShape_pempty (B : BigFppfSite.{u}) :
    (schemeSizeBelow B.cutoff).IsClosedUnderColimitsOfShape (Discrete PEmpty.{1}) :=
  haveI := schemeSizeBelow_isClosedUnderColimitsOfShape_discrete
    B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
    (ι := ULift.{u} PEmpty.{1}) (by simp)
  ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
    (Discrete.equivalence Equiv.ulift)

/-! ### Binary coproducts of schemes as clopen decompositions -/

/-- A binary coproduct cocone of schemes is, up to isomorphism, the standard one. -/
lemma exists_iso_of_isColimit_binaryCofan {X Y P : Scheme.{u}} {f : X ⟶ P} {g : Y ⟶ P}
    (hc : IsColimit (BinaryCofan.mk f g)) :
    ∃ e : (X ⨿ Y : Scheme.{u}) ≅ P,
      Limits.coprod.inl ≫ e.hom = f ∧ Limits.coprod.inr ≫ e.hom = g :=
  ⟨(coprodIsCoprod X Y).coconePointUniqueUpToIso hc,
    (coprodIsCoprod X Y).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.left⟩,
    (coprodIsCoprod X Y).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.right⟩⟩

/-- In any binary coproduct cocone of schemes the left injection is an open immersion. -/
lemma isOpenImmersion_left_of_isColimit_binaryCofan {X Y P : Scheme.{u}} {f : X ⟶ P} {g : Y ⟶ P}
    (hc : IsColimit (BinaryCofan.mk f g)) : IsOpenImmersion f := by
  obtain ⟨e, hl, -⟩ := exists_iso_of_isColimit_binaryCofan hc
  exact hl ▸ inferInstance

/-- In any binary coproduct cocone of schemes the right injection is an open immersion. -/
lemma isOpenImmersion_right_of_isColimit_binaryCofan {X Y P : Scheme.{u}} {f : X ⟶ P} {g : Y ⟶ P}
    (hc : IsColimit (BinaryCofan.mk f g)) : IsOpenImmersion g := by
  obtain ⟨e, -, hr⟩ := exists_iso_of_isColimit_binaryCofan hc
  exact hr ▸ inferInstance

/-- The two injections of a binary coproduct cocone of schemes never take the same value. -/
lemma ne_of_isColimit_binaryCofan {X Y P : Scheme.{u}} {f : X ⟶ P} {g : Y ⟶ P}
    (hc : IsColimit (BinaryCofan.mk f g)) (a : X) (b : Y) : f a ≠ g b := by
  obtain ⟨e, hl, hr⟩ := exists_iso_of_isColimit_binaryCofan hc
  intro h
  rw [← hl, ← hr, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
  exact inl_ne_inr X Y a b (e.hom.homeomorph.injective h)

/-- The images of the two injections of a binary coproduct cocone of schemes cover the
coproduct. -/
lemma exists_eq_or_exists_eq_of_isColimit_binaryCofan {X Y P : Scheme.{u}} {f : X ⟶ P}
    {g : Y ⟶ P} (hc : IsColimit (BinaryCofan.mk f g)) (x : P) :
    (∃ a, f a = x) ∨ (∃ b, g b = x) := by
  obtain ⟨e, hl, hr⟩ := exists_iso_of_isColimit_binaryCofan hc
  obtain ⟨y, rfl⟩ := e.hom.homeomorph.surjective x
  obtain ⟨z, hz⟩ := (coprodMk X Y).surjective y
  cases z with
  | inl a =>
      refine Or.inl ⟨a, ?_⟩
      rw [← hl, Scheme.Hom.comp_apply, ← coprodMk_inl, hz]
      rfl
  | inr b =>
      refine Or.inr ⟨b, ?_⟩
      rw [← hr, Scheme.Hom.comp_apply, ← coprodMk_inr, hz]
      rfl

section Over

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big fppf site over `S` has a final object. -/
instance hasTerminal_bigFppfOver : HasTerminal (BigFppfOver B S hS) :=
  Over.mkIdTerminal.hasTerminal

/-- The functor to schemes from the big fppf site over `S` preserves binary coproducts. -/
instance preservesBinaryCoproducts_bigFppfOverToScheme :
    PreservesColimitsOfShape (Discrete WalkingPair) (BigFppfOver.toScheme B S hS) := by
  infer_instance

/-- The functor to schemes from the big fppf site over `S` preserves the initial object. -/
instance preservesInitial_bigFppfOverToScheme :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (BigFppfOver.toScheme B S hS) := by
  infer_instance

end Over

/-! ### Open subobjects of the big fppf site -/

section Restrict

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The functor to schemes from the big fppf site over `S` is faithful. -/
instance faithful_bigFppfOverToScheme : (BigFppfOver.toScheme B S hS).Faithful := by
  infer_instance

/-- An open subscheme of an object of the big fppf site over `S` is again an object of that
site, and its inclusion is a morphism of the site. Any morphism of the site into `X` whose image
lies in the open subscheme factors through the inclusion. -/
lemma exists_restrict_bigFppfOver (X : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj X).Opens) :
    ∃ (Y : BigFppfOver B S hS) (f : Y ⟶ X),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map f) ∧
        Set.range ((BigFppfOver.toScheme B S hS).map f) = (W : Set _) ∧
        ∀ {X' : BigFppfOver B S hS} (g : X' ⟶ X),
          Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆ (W : Set _) →
            ∃ h : X' ⟶ Y, h ≫ f = g := by
  refine ⟨Over.mk (show (⟨W.toScheme,
      Scheme.size_lt_of_isOpenImmersion W.ι X.left.property⟩ : B.Schemes) ⟶ B.obj hS from
      ObjectProperty.homMk W.ι ≫ X.hom), Over.homMk (ObjectProperty.homMk W.ι) rfl, ?_, ?_, ?_⟩
  · exact inferInstanceAs (IsOpenImmersion W.ι)
  · exact W.range_ι
  · intro X' g hg
    have hr : Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆ Set.range W.ι := by
      rwa [W.range_ι]
    refine ⟨Over.homMk (ObjectProperty.homMk
      (IsOpenImmersion.lift W.ι ((BigFppfOver.toScheme B S hS).map g) hr)) ?_, ?_⟩
    · refine B.inclusion.map_injective ?_
      have hw := congrArg B.inclusion.map (Over.w g)
      simp only [Functor.map_comp] at hw ⊢
      show (IsOpenImmersion.lift W.ι ((BigFppfOver.toScheme B S hS).map g) hr ≫ W.ι) ≫
        B.inclusion.map X.hom = B.inclusion.map X'.hom
      rw [IsOpenImmersion.lift_fac]
      exact hw
    · refine (BigFppfOver.toScheme B S hS).map_injective ?_
      rw [Functor.map_comp]
      show IsOpenImmersion.lift W.ι ((BigFppfOver.toScheme B S hS).map g) hr ≫ W.ι = _
      exact IsOpenImmersion.lift_fac _ _ hr

end Restrict

/-! ### A colimit cofan in the big fppf site is a disjoint open cover -/

section Colimit

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type v} {U : I → BigFppfOver B S hS} {V : BigFppfOver B S hS}
  {j : ∀ i, U i ⟶ V}

/-- The image in schemes of a binary coproduct of the big fppf site over `S` is a binary
coproduct of schemes. -/
noncomputable def isColimitBinaryCofanToSchemeMap (X Y : BigFppfOver B S hS) :
    IsColimit (BinaryCofan.mk
      ((BigFppfOver.toScheme B S hS).map (Limits.coprod.inl : X ⟶ X ⨿ Y))
      ((BigFppfOver.toScheme B S hS).map (Limits.coprod.inr : Y ⟶ X ⨿ Y))) :=
  isColimitOfHasBinaryCoproductOfPreservesColimit _ X Y

section Sel

variable [DecidableEq I]

/-- Given a colimit cofan `V` of the family `U` in the big fppf site over `S` and an index
`i₀`, the morphism `V ⟶ V ⨿ V` which sends the `i₀`-th member into the left summand and
every other member into the right summand. Its two "fibres" are the complementary open
subschemes of `V` separating the `i₀`-th member from the rest. -/
noncomputable def cofanSel (hV : IsColimit (Cofan.mk V j)) (i₀ : I) : V ⟶ V ⨿ V :=
  Cofan.IsColimit.desc hV fun i =>
    j i ≫ (if i = i₀ then (Limits.coprod.inl : V ⟶ V ⨿ V) else Limits.coprod.inr)

@[simp]
lemma cofanSel_fac_self (hV : IsColimit (Cofan.mk V j)) (i₀ : I) :
    j i₀ ≫ cofanSel hV i₀ = j i₀ ≫ Limits.coprod.inl := by
  simpa [cofanSel] using Cofan.IsColimit.fac hV (fun i =>
    j i ≫ (if i = i₀ then (Limits.coprod.inl : V ⟶ V ⨿ V) else Limits.coprod.inr)) i₀

@[simp]
lemma cofanSel_fac_ne (hV : IsColimit (Cofan.mk V j)) {i i₀ : I} (hi : i ≠ i₀) :
    j i ≫ cofanSel hV i₀ = j i ≫ Limits.coprod.inr := by
  simpa [cofanSel, hi] using Cofan.IsColimit.fac hV (fun i =>
    j i ≫ (if i = i₀ then (Limits.coprod.inl : V ⟶ V ⨿ V) else Limits.coprod.inr)) i

end Sel

/-- Points of `V` coming from morphisms into `V` that `c : V ⟶ V ⨿ V` sends into the left
and the right summand respectively are distinct. -/
private theorem toScheme_map_ne_of_comp_eq_inl_inr {P Q : BigFppfOver B S hS} {c : V ⟶ V ⨿ V}
    {a a' b b' : _ ⟶ V} (ha : a ≫ c = a' ≫ Limits.coprod.inl) (hb : b ≫ c = b' ≫ Limits.coprod.inr)
    (x : (BigFppfOver.toScheme B S hS).obj P) (y : (BigFppfOver.toScheme B S hS).obj Q) :
    (BigFppfOver.toScheme B S hS).map a x ≠ (BigFppfOver.toScheme B S hS).map b y := by
  intro h
  have h₁ := congrArg ((BigFppfOver.toScheme B S hS).map c) h
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
    ha, hb, Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply] at h₁
  exact ne_of_isColimit_binaryCofan (isColimitBinaryCofanToSchemeMap V V) _ _ h₁

/-- Distinct members of a colimit cofan in the big fppf site over `S` have disjoint images
in the underlying scheme. -/
lemma ne_toScheme_map_cofan (hV : IsColimit (Cofan.mk V j)) {i i' : I} (hii' : i ≠ i')
    (z : (BigFppfOver.toScheme B S hS).obj (U i))
    (z' : (BigFppfOver.toScheme B S hS).obj (U i')) :
    (BigFppfOver.toScheme B S hS).map (j i) z ≠
      (BigFppfOver.toScheme B S hS).map (j i') z' := by
  classical
  exact (toScheme_map_ne_of_comp_eq_inl_inr (cofanSel_fac_self hV i')
    (cofanSel_fac_ne hV hii') z' z).symm

/-- A member of a colimit cofan in the big fppf site over `S` factors as an isomorphism onto an
open subscheme of `V`, on underlying schemes. -/
lemma exists_isOpenImmersion_factorisation_of_isColimit_cofan
    (hV : IsColimit (Cofan.mk V j)) (i₀ : I) :
    ∃ (Y : BigFppfOver B S hS) (q : Y ⟶ V) (a : U i₀ ⟶ Y),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map q) ∧
        IsIso ((BigFppfOver.toScheme B S hS).map a) ∧ a ≫ q = j i₀ := by
  classical
  have hinl : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (Limits.coprod.inl : V ⟶ V ⨿ V)) :=
    isOpenImmersion_left_of_isColimit_binaryCofan (isColimitBinaryCofanToSchemeMap V V)
  have hq : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (Limits.pullback.fst (cofanSel hV i₀) (Limits.coprod.inl : V ⟶ V ⨿ V))) := by
    rw [← PreservesPullback.iso_hom_fst (BigFppfOver.toScheme B S hS) (cofanSel hV i₀)
      (Limits.coprod.inl : V ⟶ V ⨿ V)]
    exact IsOpenImmersion.comp _ _
  have hdisj : ∀ (y : (BigFppfOver.toScheme B S hS).obj
        (Limits.pullback (cofanSel hV i₀) (Limits.coprod.inl : V ⟶ V ⨿ V)))
      (t : (BigFppfOver.toScheme B S hS).obj
        (Limits.pullback (cofanSel hV i₀) (Limits.coprod.inr : V ⟶ V ⨿ V))),
      (BigFppfOver.toScheme B S hS).map
          (Limits.pullback.fst (cofanSel hV i₀) (Limits.coprod.inl : V ⟶ V ⨿ V)) y ≠
        (BigFppfOver.toScheme B S hS).map
          (Limits.pullback.fst (cofanSel hV i₀) (Limits.coprod.inr : V ⟶ V ⨿ V)) t :=
    toScheme_map_ne_of_comp_eq_inl_inr Limits.pullback.condition Limits.pullback.condition
  set g : ∀ i, U i ⟶ U i₀ ⨿ Limits.pullback (cofanSel hV i₀)
      (Limits.coprod.inr : V ⟶ V ⨿ V) := fun i =>
    if h : i = i₀ then eqToHom (congrArg U h) ≫ Limits.coprod.inl
      else Limits.pullback.lift (j i) (j i) (cofanSel_fac_ne hV h) ≫ Limits.coprod.inr with hg
  set χ := Cofan.IsColimit.desc hV g with hχ
  set d := Limits.coprod.desc (j i₀)
    (Limits.pullback.fst (cofanSel hV i₀) (Limits.coprod.inr : V ⟶ V ⨿ V)) with hd
  have hfac : ∀ i, j i ≫ χ = g i := fun i => by simpa using Cofan.IsColimit.fac hV g i
  have hgi₀ : g i₀ = Limits.coprod.inl := by simp [hg]
  have hdχ : χ ≫ d = 𝟙 V := by
    refine Cofan.IsColimit.hom_ext hV _ _ fun i => ?_
    simp only [cofan_mk_inj, ← Category.assoc, hfac i]
    by_cases h : i = i₀
    · subst h
      simp [hgi₀, hd, Limits.coprod.inl_desc]
    · simp [hg, h, hd, Limits.coprod.inr_desc, Limits.pullback.lift_fst]
  have hχi₀ : j i₀ ≫ χ = Limits.coprod.inl := by rw [hfac i₀, hgi₀]
  have hinlW : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (Limits.coprod.inl :
      U i₀ ⟶ U i₀ ⨿ Limits.pullback (cofanSel hV i₀)
        (Limits.coprod.inr : V ⟶ V ⨿ V))) :=
    isOpenImmersion_left_of_isColimit_binaryCofan
      (isColimitBinaryCofanToSchemeMap (U i₀) _)
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map
      (Limits.pullback.fst (cofanSel hV i₀) (Limits.coprod.inl : V ⟶ V ⨿ V) ≫ χ)) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map (Limits.coprod.inl :
        U i₀ ⟶ U i₀ ⨿ Limits.pullback (cofanSel hV i₀)
          (Limits.coprod.inr : V ⟶ V ⨿ V))) := by
    rintro _ ⟨y, rfl⟩
    rcases exists_eq_or_exists_eq_of_isColimit_binaryCofan
      (isColimitBinaryCofanToSchemeMap (U i₀) (Limits.pullback (cofanSel hV i₀)
        (Limits.coprod.inr : V ⟶ V ⨿ V)))
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst (cofanSel hV i₀)
        (Limits.coprod.inl : V ⟶ V ⨿ V) ≫ χ) y) with ⟨s, hs⟩ | ⟨t, ht⟩
    · exact ⟨s, hs⟩
    · refine absurd ?_ (hdisj y t)
      have e1 : (BigFppfOver.toScheme B S hS).map
            (Limits.pullback.fst (cofanSel hV i₀) (Limits.coprod.inl : V ⟶ V ⨿ V)) y =
          (BigFppfOver.toScheme B S hS).map d
            ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst (cofanSel hV i₀)
              (Limits.coprod.inl : V ⟶ V ⨿ V) ≫ χ) y) := by
        rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, Category.assoc, hdχ, Category.comp_id]
      have e2 : (BigFppfOver.toScheme B S hS).map d
            ((BigFppfOver.toScheme B S hS).map (Limits.coprod.inr :
              Limits.pullback (cofanSel hV i₀) (Limits.coprod.inr : V ⟶ V ⨿ V) ⟶
                U i₀ ⨿ Limits.pullback (cofanSel hV i₀)
                  (Limits.coprod.inr : V ⟶ V ⨿ V)) t) =
          (BigFppfOver.toScheme B S hS).map
            (Limits.pullback.fst (cofanSel hV i₀) (Limits.coprod.inr : V ⟶ V ⨿ V)) t := by
        rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hd, Limits.coprod.inr_desc]
      rw [e1, ← ht, e2]
  obtain ⟨ρ, hρfac⟩ : ∃ ρ, ρ ≫ (BigFppfOver.toScheme B S hS).map (Limits.coprod.inl :
      U i₀ ⟶ U i₀ ⨿ Limits.pullback (cofanSel hV i₀)
        (Limits.coprod.inr : V ⟶ V ⨿ V)) =
      (BigFppfOver.toScheme B S hS).map (Limits.pullback.fst (cofanSel hV i₀)
        (Limits.coprod.inl : V ⟶ V ⨿ V) ≫ χ) :=
    ⟨IsOpenImmersion.lift _ _ hrange, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hai : Limits.pullback.lift (j i₀) (j i₀) (cofanSel_fac_self hV i₀) ≫
      Limits.pullback.fst (cofanSel hV i₀) (Limits.coprod.inl : V ⟶ V ⨿ V) = j i₀ :=
    Limits.pullback.lift_fst _ _ _
  have hmonoW : Mono ((BigFppfOver.toScheme B S hS).map (Limits.coprod.inl :
      U i₀ ⟶ U i₀ ⨿ Limits.pullback (cofanSel hV i₀)
        (Limits.coprod.inr : V ⟶ V ⨿ V))) := IsOpenImmersion.mono _
  have hmonoq : Mono ((BigFppfOver.toScheme B S hS).map
      (Limits.pullback.fst (cofanSel hV i₀) (Limits.coprod.inl : V ⟶ V ⨿ V))) :=
    IsOpenImmersion.mono _
  refine ⟨Limits.pullback (cofanSel hV i₀) (Limits.coprod.inl : V ⟶ V ⨿ V),
    Limits.pullback.fst _ _,
    Limits.pullback.lift (j i₀) (j i₀) (cofanSel_fac_self hV i₀), hq, ⟨ρ, ?_, ?_⟩, hai⟩
  · rw [← cancel_mono ((BigFppfOver.toScheme B S hS).map (Limits.coprod.inl :
      U i₀ ⟶ U i₀ ⨿ Limits.pullback (cofanSel hV i₀)
        (Limits.coprod.inr : V ⟶ V ⨿ V)))]
    rw [Category.assoc, hρfac, Category.id_comp, ← Functor.map_comp, ← Category.assoc,
      hai, hχi₀]
  · rw [← cancel_mono ((BigFppfOver.toScheme B S hS).map
      (Limits.pullback.fst (cofanSel hV i₀) (Limits.coprod.inl : V ⟶ V ⨿ V)))]
    rw [Category.assoc, ← Functor.map_comp, hai, Category.id_comp]
    have hji₀ : (BigFppfOver.toScheme B S hS).map (j i₀) =
        (BigFppfOver.toScheme B S hS).map (Limits.coprod.inl : U i₀ ⟶ U i₀ ⨿
          Limits.pullback (cofanSel hV i₀) (Limits.coprod.inr : V ⟶ V ⨿ V)) ≫
          (BigFppfOver.toScheme B S hS).map d := by
      rw [← Functor.map_comp, hd, Limits.coprod.inl_desc]
    rw [hji₀, ← Category.assoc, hρfac, ← Functor.map_comp, Category.assoc, hdχ,
      Category.comp_id]

/-- Each member of a colimit cofan in the big fppf site over `S` is an open immersion on
underlying schemes. -/
lemma isOpenImmersion_toScheme_map_cofan (hV : IsColimit (Cofan.mk V j)) (i₀ : I) :
    IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i₀)) := by
  obtain ⟨Y, q, a, hq, ha, hfac⟩ :=
    exists_isOpenImmersion_factorisation_of_isColimit_cofan hV i₀
  rw [← hfac, Functor.map_comp]
  exact IsOpenImmersion.comp _ _

/-- The members of a colimit cofan in the big fppf site over `S` jointly cover `V` on
underlying schemes. -/
lemma iUnion_range_toScheme_map_cofan (hV : IsColimit (Cofan.mk V j)) :
    (⋃ i, Set.range ((BigFppfOver.toScheme B S hS).map (j i))) = Set.univ := by
  classical
  have hoi : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)) := fun i =>
    isOpenImmersion_toScheme_map_cofan hV i
  have hopen : IsOpen (⋃ i, Set.range ((BigFppfOver.toScheme B S hS).map (j i))) :=
    isOpen_iUnion fun i => (hoi i).base_open.isOpen_range
  obtain ⟨Y, f, hf, hfr, huniv⟩ := exists_restrict_bigFppfOver V
    ⟨⋃ i, Set.range ((BigFppfOver.toScheme B S hS).map (j i)), hopen⟩
  choose k hk using fun i => huniv (j i)
    (Set.subset_iUnion
      (fun i => Set.range ((BigFppfOver.toScheme B S hS).map (j i))) i)
  have hsec : Cofan.IsColimit.desc hV k ≫ f = 𝟙 V := by
    refine Cofan.IsColimit.hom_ext hV _ _ fun i => ?_
    rw [← Category.assoc, Cofan.IsColimit.fac hV k i, hk i]
    simp
  have hsurj : Set.range ((BigFppfOver.toScheme B S hS).map f) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    refine ⟨(BigFppfOver.toScheme B S hS).map (Cofan.IsColimit.desc hV k) x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hsec]
    simp
  exact hfr.symm.trans hsurj

/-- For a small index type, a colimit cofan in the big fppf site over `S` is also a colimit
cofan in the category of all schemes. -/
lemma nonempty_isColimit_cofan_toScheme [Small.{u} I] (hV : IsColimit (Cofan.mk V j)) :
    Nonempty (IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj V)
      fun i => (BigFppfOver.toScheme B S hS).map (j i))) := by
  have hoi : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)) := fun i =>
    isOpenImmersion_toScheme_map_cofan hV i
  refine nonempty_isColimit_cofanMk_of _ ?_ ?_
  · refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    simpa only [Scheme.Hom.coe_opensRange] using iUnion_range_toScheme_map_cofan hV
  · intro i i' hii'
    simp only [Function.onFun]
    rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_iff_inter_eq_empty]
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩
    exact ne_toScheme_map_cofan hV hii' z z' (hz.trans hz'.symm)

end Colimit

end AlgebraicGeometry

end

