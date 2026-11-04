module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf

/-!
# Extending functors from a full subcategory of schemes: the limit condition and uniqueness

This file is the first of the three parts of
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsLimits`: it contains the filteredness
of the index category of the colimit formula, the first case of the analogue of condition (b),
the comparison of the colimit formula with the extension on affine objects, and the inverse
systems of open subobjects. The analogue of condition (b) for the extension is in
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsLimits.LimitCondition`, and the
restriction to `𝒞`, existence and uniqueness are in
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsLimits.Uniqueness`.

Let `S` be a scheme, let `𝒞` be a full subcategory of `Sch/S` satisfying conditions (1) and (2)
of Stacks 0EUW, and let `F : 𝒞ᵒᵖ ⥤ Set` satisfy conditions (a) and (b). The extension
`F' = AlgebraicGeometry.ExtendingFunctors.extension` of `F` to `Sch/S` is constructed in
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsExistence` and shown to be a Zariski
sheaf in `StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf`. This file proves the
analogue of condition (b) for `F'`, identifies the restriction of `F'` to `𝒞` with `F`, and
deduces the existence and uniqueness of the extension.

## The three steps

Condition (b) is proved in the two cases of the source. For an inverse system of affine objects
lying over affine opens of `S` the colimit formula computes the limit by the cofinality of
Stacks 01ZC, which is `nonempty_isColimit_affineExtension`. In general the least stage of the
system is covered by finitely many affine opens lying over affine opens of `S`, the inverse
systems of their inverse images are of the previous kind, and the colimit over the system
interchanges with the sheaf condition; this is `preservesAffineLimits_extension`.

The restriction of `F'` to `𝒞` is identified with `F` by covering an object of `𝒞` by its affine
opens lying over affine opens of `S`, where `F'` is computed by the colimit formula, and gluing
with condition (a); here the coverings of the pairwise intersections required by the footnote of
the source are genuinely needed. This is `nonempty_restrictionIso`.

The uniqueness of the extension uses both halves of the construction: a functor `F''` satisfying
the analogue of (b) receives a map from the colimit formula by the universal property of the left
Kan extension, that map is bijective on the affine objects over affine opens of `S` by condition
(b) for `F''`, and the universal property of the right Kan extension then produces a map
`F'' ⟶ F'` which the sheaf condition on both sides makes bijective everywhere.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.overOpenAt`,
  `AlgebraicGeometry.ExtendingFunctors.overOpenDiagram`,
  `AlgebraicGeometry.ExtendingFunctors.overOpenCone`: for an inverse system in `Sch/S` indexed by
  the opposite of a poset with a least element and an open of the least stage, the inverse
  system of the corresponding open subobjects of the stages and its cone over the corresponding
  open subobject of the limit.
* `AlgebraicGeometry.ExtendingFunctors.toExtension`: the identification of the colimit formula
  with the extension on an affine object lying over an affine open of `S`, read as a map into the
  extension.
* `AlgebraicGeometry.ExtendingFunctors.affineExtensionToF`: the comparison of the colimit formula
  with `F` on an object of the subcategory.
* `AlgebraicGeometry.ExtendingFunctors.restrictionApp`,
  `AlgebraicGeometry.ExtendingFunctors.restrictionHom`: the identification of the restriction of
  the extension to the subcategory with `F`.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.isFiltered_arrowsInto`: the index category of the colimit
  formula is filtered at an affine object lying over an affine open of `S`.
* `AlgebraicGeometry.ExtendingFunctors.nonempty_isColimit_affineExtension`: the first case of the
  analogue of condition (b) for the colimit formula.
* `AlgebraicGeometry.ExtendingFunctors.isLimitOverOpenCone`: the open subobjects of the stages of
  an inverse system of affine objects over an open of the least stage have the corresponding open
  subobject of the limit as their limit.
* `AlgebraicGeometry.ExtendingFunctors.preservesAffineLimits_extension`: the analogue of condition
  (b) for the extension.
* `AlgebraicGeometry.ExtendingFunctors.existsUnique_glue_of_cover`: condition (a) for a covering
  by affine opens whose pairwise intersections are themselves covered by affine opens.
* `AlgebraicGeometry.ExtendingFunctors.nonempty_restrictionIso`: the restriction of the extension
  to the subcategory is `F`.
* `AlgebraicGeometry.ExtendingFunctors.exists_unique_extension`: the statement of Stacks 0EUW.

## Implementation notes

The open subobjects of the stages of an inverse system are written both as the values of the
inverse system `overOpenDiagram` and directly as `overOpen` of the opens `overOpenAt`; the two
descriptions are definitionally equal but not syntactically so, and the interchange argument
compares morphisms between them, so the inverse system and its cone unfold at `implicit`
transparency inside the proof of `nonempty_isColimit_extension_of_orderBot`.

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.ExtendingFunctors

universe v w u

variable {S : Scheme.{u}}

/-! ### The index category of the colimit formula is filtered -/

/-- **The index category of the colimit formula is filtered.** For an affine object of `Sch/S`
lying over an affine open of `S`, the category of arrows from it into the objects of the
subcategory which are locally of finite presentation over `S` is filtered, because a presentation
of that object is a cofinal diagram in it indexed by a directed poset. -/
theorem isFiltered_arrowsInto {P : ObjectProperty (Over S)}
    (hP2 : HasFinitePresentationAffines P) (X : Over S) (hX : IsAffineOverAffineOpen X) :
    IsFiltered (ArrowsInto P X) := by
  classical
  obtain ⟨Λ, _, _, _, D, c, hc, ci, haff⟩ := exists_lfpPresentation hP2 X hX
  have hfin := final_presentationArrows c hc ci haff
  obtain ⟨h₁, h₂⟩ := (Functor.final_iff_of_isFiltered (presentationArrows c ci)).1 hfin
  have hne : Nonempty (ArrowsInto P X) :=
    ⟨(presentationArrows c ci).obj (Classical.arbitrary Λ)⟩
  have hfe : IsFilteredOrEmpty (ArrowsInto P X) := by
    constructor
    · intro d d'
      obtain ⟨l, ⟨f⟩⟩ := h₁ d
      obtain ⟨l', ⟨f'⟩⟩ := h₁ d'
      obtain ⟨m, hlm, hl'm⟩ := exists_ge_ge l l'
      exact ⟨(presentationArrows c ci).obj m, f ≫ (presentationArrows c ci).map (homOfLE hlm),
        f' ≫ (presentationArrows c ci).map (homOfLE hl'm), trivial⟩
    · intro d d' f g
      obtain ⟨l, ⟨h⟩⟩ := h₁ d'
      obtain ⟨l', t, ht⟩ := h₂ (f ≫ h) (g ≫ h)
      refine ⟨(presentationArrows c ci).obj l', h ≫ (presentationArrows c ci).map t, ?_⟩
      rw [← Category.assoc, ← Category.assoc]
      exact ht
  exact { nonempty := hne }

/-! ### Elements of the colimit formula -/

section Elements

variable {P : ObjectProperty (Over S)} (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))

/-- Every element of the colimit `colim_{X → V'} F(V')` is in the image of one of its legs. -/
theorem exists_affineExtensionι_eq_of_arrow (X : Over S)
    (x : (affineExtension P F).obj (op X)) :
    ∃ (A : (lfpPart P).FullSubcategory) (f : X ⟶ A.obj)
      (y : (lfpRestriction P F).obj (op A)), affineExtensionι P F A f y = x :=
  (Types.jointly_surjective_of_isColimit (colimit.isColimit
    (CostructuredArrow.proj (lfpPart P).ι.op (op X) ⋙ lfpRestriction P F)) x).elim
      fun d ⟨y, hy⟩ => ⟨d.left.unop, d.hom.unop, y, hy⟩

/-- Two elements of the colimit `colim_{X → V'} F(V')` over an affine object lying over an affine
open of `S` are in the image of a single leg. -/
theorem exists_affineExtensionι_eq_of_arrow₂ (hP2 : HasFinitePresentationAffines P)
    (X : Over S) (hX : IsAffineOverAffineOpen X) (x x' : (affineExtension P F).obj (op X)) :
    ∃ (A : (lfpPart P).FullSubcategory) (f : X ⟶ A.obj)
      (y y' : (lfpRestriction P F).obj (op A)),
      affineExtensionι P F A f y = x ∧ affineExtensionι P F A f y' = x' := by
  have := isFiltered_arrowsInto hP2 X hX
  obtain ⟨d, y, y', hy, hy'⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (colimit.isColimit (CostructuredArrow.proj (lfpPart P).ι.op (op X) ⋙ lfpRestriction P F))
    x x'
  exact ⟨d.left.unop, d.hom.unop, y, y', hy, hy'⟩

/-- Two sections whose images under a single leg of the colimit `colim_{X → V'} F(V')` agree
already agree after passing to a further arrow out of `X`. -/
theorem exists_map_eq_of_affineExtensionι_eq_of_arrow (hP2 : HasFinitePresentationAffines P)
    (X : Over S) (hX : IsAffineOverAffineOpen X) {A : (lfpPart P).FullSubcategory}
    (f : X ⟶ A.obj) (y y' : (lfpRestriction P F).obj (op A))
    (h : affineExtensionι P F A f y = affineExtensionι P F A f y') :
    ∃ (B : (lfpPart P).FullSubcategory) (g : X ⟶ B.obj) (k : B ⟶ A),
      g ≫ (lfpPart P).ι.map k = f ∧
        (lfpRestriction P F).map k.op y = (lfpRestriction P F).map k.op y' := by
  have := isFiltered_arrowsInto hP2 X hX
  obtain ⟨d, φ, hφ⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (F := CostructuredArrow.proj (lfpPart P).ι.op (op X) ⋙ lfpRestriction P F)
    (colimit.isColimit _) (i := CostructuredArrow.mk (Y := op A) f.op) y y').1 h
  refine ⟨d.left.unop, d.hom.unop, φ.left.unop, ?_, hφ⟩
  exact congrArg Quiver.Hom.unop (CostructuredArrow.w φ)

end Elements

/-! ### The analogue of condition (b) for affine objects over an affine open -/

/-- **Case A of the analogue of condition (b) of Stacks 0EUW.** A directed inverse limit of
affine objects of `Sch/S` lying over affine opens of `S`, whose limit again lies over an affine
open of `S`, is carried by the colimit formula to a filtered colimit.

This is the cofinality argument of Stacks 01ZC: a morphism out of the limit into an object
locally of finite presentation over `S` factors through a stage of the system, and two such
factorizations agreeing over the limit already agree at a later stage. -/
theorem nonempty_isColimit_affineExtension {P : ObjectProperty (Over S)}
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) (hP2 : HasFinitePresentationAffines P)
    {Λ : Type u} [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ] (D : Λᵒᵖ ⥤ Over S)
    (hD : ∀ l, IsAffineOverAffineOpen (D.obj l)) (c : Cone D) (hc : IsLimit c)
    (hcpt : IsAffineOverAffineOpen c.pt) :
    Nonempty (IsColimit ((affineExtension P F).mapCocone c.op)) := by
  classical
  have hDaff : ∀ l, IsAffine (D.obj l).left := fun l => (hD l).1
  have hpres : ∀ A : (lfpPart P).FullSubcategory,
      Scheme.IsLimitPreserving S (yoneda.obj A.obj) := by
    intro A
    have : LocallyOfFinitePresentation A.obj.hom := A.property.2
    exact Scheme.isLimitPreserving_yoneda_of_locallyOfFinitePresentation A.obj
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?_ ?_⟩
  · intro x
    obtain ⟨A, f, y, hy⟩ := exists_affineExtensionι_eq_of_arrow F c.pt x
    obtain ⟨l, g, hg⟩ := Scheme.exists_comp_eq_of_isLimitPreserving (hpres A) D c hc hDaff f
    refine ⟨op l, affineExtensionι P F A g y, ?_⟩
    rw [← hy, ← hg, ← affineExtensionι_naturality]
    rfl
  · intro l x y hxy
    obtain ⟨A, f, x₁, y₁, hx₁, hy₁⟩ :=
      exists_affineExtensionι_eq_of_arrow₂ F hP2 (D.obj l.unop) (hD l.unop) x y
    have hkey : affineExtensionι P F A (c.π.app l.unop ≫ f) x₁
        = affineExtensionι P F A (c.π.app l.unop ≫ f) y₁ := by
      rw [← affineExtensionι_naturality, ← affineExtensionι_naturality, hx₁, hy₁]
      exact hxy
    obtain ⟨B, g, k, hgk, hk⟩ := exists_map_eq_of_affineExtensionι_eq_of_arrow F hP2 c.pt hcpt
      (c.π.app l.unop ≫ f) x₁ y₁ hkey
    obtain ⟨m, gm, hgm⟩ := Scheme.exists_comp_eq_of_isLimitPreserving (hpres B) D c hc hDaff g
    obtain ⟨n, hln, hmn⟩ := exists_ge_ge l.unop.unop m.unop
    set α : (op n : Λᵒᵖ) ⟶ l.unop := (homOfLE hln).op with hα
    set β : (op n : Λᵒᵖ) ⟶ m := (homOfLE hmn).op with hβ
    have heq : c.π.app (op n) ≫ (D.map α ≫ f)
        = c.π.app (op n) ≫ (D.map β ≫ gm ≫ (lfpPart P).ι.map k) := by
      rw [← Category.assoc, ← Category.assoc, c.w α, c.w β, ← Category.assoc, hgm, hgk]
    obtain ⟨p, γ, hγ⟩ := exists_map_comp_eq_of_isLimitPreserving (hpres A) D c hc hDaff
      (D.map α ≫ f) (D.map β ≫ gm ≫ (lfpPart P).ι.map k) heq
    refine ⟨op p, (γ ≫ α).op, ?_⟩
    have hfac : D.map (γ ≫ α) ≫ f
        = (D.map (γ ≫ β) ≫ gm) ≫ (lfpPart P).ι.map k := by
      rw [D.map_comp, D.map_comp, Category.assoc, Category.assoc, Category.assoc, hγ]
    have hrw : ∀ z : (lfpRestriction P F).obj (op A),
        (affineExtension P F).map (D.map (γ ≫ α)).op (affineExtensionι P F A f z)
          = affineExtensionι P F B (D.map (γ ≫ β) ≫ gm)
            ((lfpRestriction P F).map k.op z) := by
      intro z
      rw [affineExtensionι_naturality, hfac, affineExtensionι_map]
    show (affineExtension P F).map (D.map (γ ≫ α)).op x
      = (affineExtension P F).map (D.map (γ ≫ α)).op y
    rw [← hx₁, ← hy₁, hrw, hrw, hk]

/-! ### Affine objects lying over an affine open of the base -/

/-- An object of `Sch/S` with affine underlying scheme admitting a morphism to an object lying
over an affine open of `S` again lies over an affine open of `S`. -/
lemma isAffineOverAffineOpen_of_hom {X Y : Over S} (f : X ⟶ Y)
    (hY : IsAffineOverAffineOpen Y) (hX : IsAffine X.left) : IsAffineOverAffineOpen X := by
  obtain ⟨-, U, g, hg⟩ := hY
  exact ⟨hX, U, f.left ≫ g, by rw [Category.assoc, hg]; exact Over.w f⟩

/-- Every point of an object of `Sch/S` has an affine open neighbourhood inside a given open
which, as an object of `Sch/S`, lies over an affine open of `S`. -/
lemma exists_isAffineOverAffineOpen_nbhd (X : Over S) (z : X.left) (O : X.left.Opens)
    (hz : z ∈ O) :
    ∃ V : X.left.Opens, IsAffineOpen V ∧ z ∈ V ∧ V ≤ O ∧
      IsAffineOverAffineOpen (overOpen X V) := by
  obtain ⟨U, V₀, hzV₀, g, hg⟩ :=
    Stacks.AlgebraicGeometry.Tag05JXGeneral.exists_affine_neighborhood_lift X.hom z
  have hmem : z ∈ V₀.1 ⊓ O := ⟨hzV₀, hz⟩
  obtain ⟨V, hVmem, hzV, hVle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.left.isBasis_affineOpens) hmem
  have hVle₀ : V ≤ V₀.1 := le_trans hVle inf_le_left
  have hVleO : V ≤ O := le_trans hVle inf_le_right
  have hrange : Set.range (⇑(Scheme.Opens.ι V ≫ X.hom)) ⊆ Set.range (⇑U.1.ι) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨g ⟨y.1, hVle₀ y.2⟩, ?_⟩
    exact congrArg (fun k : V₀.1.toScheme ⟶ S => k.base ⟨y.1, hVle₀ y.2⟩) hg
  refine ⟨V, hVmem, hzV, hVleO, hVmem, U,
    IsOpenImmersion.lift U.1.ι (Scheme.Opens.ι V ≫ X.hom) hrange, ?_⟩
  exact IsOpenImmersion.lift_fac _ _ _

/-- A quasi-compact object of `Sch/S` has a finite covering by affine opens which, as objects of
`Sch/S`, lie over affine opens of `S`. -/
lemma exists_finite_isAffineOverAffineOpen_cover (X : Over S) [CompactSpace X.left] :
    ∃ (κ : Type u) (_ : Finite κ) (W : κ → X.left.Opens),
      (⨆ a, W a = ⊤) ∧ (∀ a, IsAffineOpen (W a)) ∧
        ∀ a, IsAffineOverAffineOpen (overOpen X (W a)) := by
  classical
  choose V hVaff hzV hVtop hVover using fun z : X.left =>
    exists_isAffineOverAffineOpen_nbhd X z ⊤ (Set.mem_univ z)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun z : X.left => (V z : Set X.left))
    (fun z => (V z).isOpen) (fun z _ => Set.mem_iUnion.mpr ⟨z, hzV z⟩)
  refine ⟨(t : Type u), inferInstance, fun a => V a.1, ?_, fun a => hVaff a.1,
    fun a => hVover a.1⟩
  refine le_antisymm le_top fun z _ => ?_
  obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hza⟩

/-! ### The extension and the colimit formula on affine objects -/

section Comparison

variable (P : ObjectProperty (Over S)) (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))

/-- The identification of the colimit formula with the extension on an affine object of `Sch/S`
lying over an affine open of `S`, read as a map into the extension. -/
noncomputable def toExtension {V : Over S} (hV : IsAffineOverAffineOpen V) :
    (affineExtension P F).obj (op V) ⟶ (extension P F).obj (op V) :=
  ((extensionIsoOnAffine P F).app (op (⟨V, hV⟩ :
    (IsAffineOverAffineOpen (S := S)).FullSubcategory))).inv

/-- The projection of the extension at the identity of an affine object lying over an affine open
of `S` is the identification of the extension with the colimit formula there. -/
lemma extensionπ_id {V : Over S} (hV : IsAffineOverAffineOpen V)
    (t : (extension P F).obj (op V)) :
    extensionπ P F hV (𝟙 V) t
      = ((extensionIsoOnAffine P F).app (op (⟨V, hV⟩ :
          (IsAffineOverAffineOpen (S := S)).FullSubcategory))).hom t :=
  rfl

/-- `toExtension` is a right inverse of the projection at the identity. -/
@[simp]
lemma extensionπ_id_toExtension {V : Over S} (hV : IsAffineOverAffineOpen V)
    (x : (affineExtension P F).obj (op V)) :
    extensionπ P F hV (𝟙 V) (toExtension P F hV x) = x := by
  exact ((extensionIsoOnAffine P F).app (op (⟨V, hV⟩ :
    (IsAffineOverAffineOpen (S := S)).FullSubcategory))).inv_hom_id_apply x

/-- `toExtension` is a left inverse of the projection at the identity. -/
@[simp]
lemma toExtension_extensionπ_id {V : Over S} (hV : IsAffineOverAffineOpen V)
    (t : (extension P F).obj (op V)) :
    toExtension P F hV (extensionπ P F hV (𝟙 V) t) = t := by
  exact ((extensionIsoOnAffine P F).app (op (⟨V, hV⟩ :
    (IsAffineOverAffineOpen (S := S)).FullSubcategory))).hom_inv_id_apply t

/-- Two sections of the extension over an affine object lying over an affine open of `S` agree as
soon as their images in the colimit formula agree. -/
lemma extension_ext_of_affine {V : Over S} (hV : IsAffineOverAffineOpen V)
    (t t' : (extension P F).obj (op V))
    (h : extensionπ P F hV (𝟙 V) t = extensionπ P F hV (𝟙 V) t') : t = t' := by
  rw [← toExtension_extensionπ_id P F hV t, ← toExtension_extensionπ_id P F hV t', h]

/-- The projection at the identity of the restriction of a section along `f` is the projection of
the section at `f`. -/
lemma extensionπ_id_map {X V : Over S} (hV : IsAffineOverAffineOpen V) (f : V ⟶ X)
    (t : (extension P F).obj (op X)) :
    extensionπ P F hV (𝟙 V) ((extension P F).map f.op t) = extensionπ P F hV f t := by
  rw [extensionπ_naturality, Category.id_comp]

end Comparison

/-! ### Separatedness of the extension -/

section Separated

variable (P : ObjectProperty (Over S)) (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))

/-- **Separatedness of the extension.** Two sections of the extension over an object of `Sch/S`
which agree on the members of an open covering are equal. -/
theorem extension_ext_of_cover (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P) (haF : IsZariskiSheafOnSubcategory P F)
    {X : Over S} {ι : Type u} (V : ι → X.left.Opens) (hcov : ⨆ i, V i = ⊤)
    (t t' : (extension P F).obj (op X))
    (h : ∀ i, (extension P F).map (overOpenι X (V i)).op t
      = (extension P F).map (overOpenι X (V i)).op t') : t = t' := by
  obtain ⟨w, -, huniq⟩ := isZariskiSheaf_extension P F hP1 hP2 haF X ι V hcov
    (fun i => (extension P F).map (overOpenι X (V i)).op t) (fun i j => by
      rw [map_map_apply, map_map_apply, overOpenLE_comp_overOpenι, overOpenLE_comp_overOpenι])
  rw [huniq t fun i => rfl, huniq t' fun i => (h i).symm]

end Separated

/-! ### The open subobjects of an inverse system in `Sch/S` -/

section OverOpenDiagram

variable {Λ : Type u} [PartialOrder Λ] [OrderBot Λ]

/-- The inverse image at the stage `l` of an open of the least stage of an inverse system in
`Sch/S` indexed by the opposite of a poset with a least element. -/
def overOpenAt (D : Λᵒᵖ ⥤ Over S) (W : (D.obj (op (⊥ : Λ))).left.Opens) (l : Λ) :
    (D.obj (op l)).left.Opens :=
  (D.map (homOfLE (bot_le : (⊥ : Λ) ≤ l)).op).left ⁻¹ᵁ W

/-- The inverse images of `W` at the stages are compatible with the transition maps. -/
lemma overOpenAt_preimage (D : Λᵒᵖ ⥤ Over S) (W : (D.obj (op (⊥ : Λ))).left.Opens)
    {l m : Λᵒᵖ} (φ : l ⟶ m) :
    (D.map φ).left ⁻¹ᵁ (overOpenAt D W m.unop) = overOpenAt D W l.unop := by
  have h : φ ≫ (homOfLE (bot_le : (⊥ : Λ) ≤ m.unop)).op
      = (homOfLE (bot_le : (⊥ : Λ) ≤ l.unop)).op := Subsingleton.elim _ _
  rw [overOpenAt, overOpenAt, ← Scheme.Hom.comp_preimage, ← Over.comp_left, ← Functor.map_comp, h]

/-- The inverse image under a leg of a cone of the inverse image of `W` at that stage is the
inverse image of `W` under the leg at the least stage. -/
lemma preimage_overOpenAt (D : Λᵒᵖ ⥤ Over S) (c : Cone D)
    (W : (D.obj (op (⊥ : Λ))).left.Opens) (l : Λᵒᵖ) :
    (c.π.app l).left ⁻¹ᵁ (overOpenAt D W l.unop) = (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W := by
  rw [overOpenAt, ← Scheme.Hom.comp_preimage, ← Over.comp_left, c.w]

/-- Taking inverse images at a stage commutes with binary intersections of opens. -/
lemma overOpenAt_inf (D : Λᵒᵖ ⥤ Over S) (W W' : (D.obj (op (⊥ : Λ))).left.Opens) (l : Λ) :
    overOpenAt D (W ⊓ W') l = overOpenAt D W l ⊓ overOpenAt D W' l :=
  rfl

/-- The inverse images at a stage of a cover of the least stage cover that stage. -/
lemma iSup_overOpenAt (D : Λᵒᵖ ⥤ Over S) {κ : Type u} (W : κ → (D.obj (op (⊥ : Λ))).left.Opens)
    (hW : ⨆ a, W a = ⊤) (l : Λ) : ⨆ a, overOpenAt D (W a) l = ⊤ := by
  have h : ⨆ a, overOpenAt D (W a) l
      = (D.map (homOfLE (bot_le : (⊥ : Λ) ≤ l)).op).left ⁻¹ᵁ (⨆ a, W a) :=
    (Scheme.Hom.preimage_iSup _ _).symm
  rw [h, hW]
  simp

/-- The structure morphisms over `S` of the open subobjects `overOpenAt D W l`. -/
noncomputable def overOpenAtToBase (D : Λᵒᵖ ⥤ Over S)
    (W : (D.obj (op (⊥ : Λ))).left.Opens) :
    (botToOver Λ ⋙ opensDiagram (D ⋙ Over.forget S) (op (⊥ : Λ)) W) ⟶
      (Functor.const Λᵒᵖ).obj S where
  app l := (overOpenAt D W l.unop).ι ≫ (D.obj l).hom
  naturality := by
    intro l m φ
    have h1 := Scheme.Hom.resLE_comp_ι ((D ⋙ Over.forget S).map φ)
      (U := overOpenAt D W m.unop) (V := overOpenAt D W l.unop)
      (le_of_eq (overOpenAt_preimage D W φ).symm)
    have h2 : (D ⋙ Over.forget S).map φ ≫ (D.obj m).hom = (D.obj l).hom := Over.w (D.map φ)
    have key : (opensDiagram (D ⋙ Over.forget S) (op (⊥ : Λ)) W).map ((botToOver Λ).map φ)
        = Scheme.Hom.resLE ((D ⋙ Over.forget S).map φ) (overOpenAt D W m.unop)
          (overOpenAt D W l.unop) (le_of_eq (overOpenAt_preimage D W φ).symm) := rfl
    simp only [Functor.comp_map, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [key]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ (D.obj m).hom) h1).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (fun k => (overOpenAt D W l.unop).ι ≫ k) h2

/-- **The inverse system of open subobjects.** The open subobjects `overOpenAt D W l` of the
stages of an inverse system in `Sch/S`, over an open `W` of the least stage. -/
noncomputable def overOpenDiagram (D : Λᵒᵖ ⥤ Over S)
    (W : (D.obj (op (⊥ : Λ))).left.Opens) : Λᵒᵖ ⥤ Over S :=
  Over.lift (botToOver Λ ⋙ opensDiagram (D ⋙ Over.forget S) (op (⊥ : Λ)) W)
    (overOpenAtToBase D W)

/-- The stage `l` of the inverse system of open subobjects is the open subobject
`overOpenAt D W l` of the stage `l` of `D`. -/
lemma overOpenDiagram_obj (D : Λᵒᵖ ⥤ Over S) (W : (D.obj (op (⊥ : Λ))).left.Opens) (l : Λᵒᵖ) :
    (overOpenDiagram D W).obj l = overOpen (D.obj l) (overOpenAt D W l.unop) :=
  rfl

/-- The inclusions of the open subobjects `overOpenAt D W l` into the stages, as a morphism of
inverse systems. -/
noncomputable def overOpenDiagramι (D : Λᵒᵖ ⥤ Over S)
    (W : (D.obj (op (⊥ : Λ))).left.Opens) : overOpenDiagram D W ⟶ D where
  app l := overOpenι (D.obj l) (overOpenAt D W l.unop)
  naturality l m φ := by
    refine Over.OverMorphism.ext ?_
    simp only [overOpenDiagram, Over.lift_map]
    exact Scheme.Hom.resLE_comp_ι _ _

/-- The legs of the cone of open subobjects of the limit are compatible with the structure
morphisms over `S`. -/
lemma overOpenCone_w (D : Λᵒᵖ ⥤ Over S) (W : (D.obj (op (⊥ : Λ))).left.Opens) (c : Cone D)
    (l : Λᵒᵖ) :
    (Cone.whisker (botToOver Λ) (opensCone (D ⋙ Over.forget S) ((Over.forget S).mapCone c)
        (op (⊥ : Λ)) W)).π.app l ≫ (overOpenAtToBase D W).app l
      = ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W).ι ≫ c.pt.hom := by
  have h1 := Scheme.Hom.resLE_comp_ι (c.π.app l).left
    (U := overOpenAt D W l.unop) (V := (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W)
    (le_of_eq (preimage_overOpenAt D c W l).symm)
  have key : (Cone.whisker (botToOver Λ)
        (opensCone (D ⋙ Over.forget S) ((Over.forget S).mapCone c) (op (⊥ : Λ)) W)).π.app l
      = Scheme.Hom.resLE (c.π.app l).left (overOpenAt D W l.unop)
        ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W) (le_of_eq (preimage_overOpenAt D c W l).symm) := rfl
  rw [key]
  show _ ≫ (overOpenAt D W l.unop).ι ≫ (D.obj l).hom = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ (D.obj l).hom) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun k => ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W).ι ≫ k) (Over.w (c.π.app l))

/-- The cone on the inverse system of open subobjects whose apex is the corresponding open
subobject of the limit. -/
noncomputable def overOpenCone (D : Λᵒᵖ ⥤ Over S) (W : (D.obj (op (⊥ : Λ))).left.Opens)
    (c : Cone D) : Cone (overOpenDiagram D W) :=
  Over.liftCone _ (overOpenAtToBase D W)
    (Cone.whisker (botToOver Λ) (opensCone (D ⋙ Over.forget S) ((Over.forget S).mapCone c)
      (op (⊥ : Λ)) W)) (((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W).ι ≫ c.pt.hom)
    (overOpenCone_w D W c)

/-- The apex of `overOpenCone D W c` is the inverse image of `W` in the apex of `c`. -/
lemma overOpenCone_pt (D : Λᵒᵖ ⥤ Over S) (W : (D.obj (op (⊥ : Λ))).left.Opens) (c : Cone D) :
    (overOpenCone D W c).pt = overOpen c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W) :=
  rfl

/-- The component of `overOpenDiagramι D W` at a stage is the inclusion of the open subobject. -/
lemma overOpenDiagramι_app (D : Λᵒᵖ ⥤ Over S) (W : (D.obj (op (⊥ : Λ))).left.Opens)
    (l : Λᵒᵖ) :
    (overOpenDiagramι D W).app l = overOpenι (D.obj l) (overOpenAt D W l.unop) :=
  rfl

/-- The inclusions of the open subobjects commute with the transition maps. -/
lemma overOpenDiagram_map_comp_overOpenι (D : Λᵒᵖ ⥤ Over S)
    (W : (D.obj (op (⊥ : Λ))).left.Opens) {l m : Λᵒᵖ} (φ : l ⟶ m) :
    (overOpenDiagram D W).map φ ≫ overOpenι (D.obj m) (overOpenAt D W m.unop)
      = overOpenι (D.obj l) (overOpenAt D W l.unop) ≫ D.map φ :=
  (overOpenDiagramι D W).naturality φ

/-- The legs of `overOpenCone D W c` are the restrictions of the legs of `c` to the open
subobjects. -/
lemma overOpenCone_π_comp_overOpenι (D : Λᵒᵖ ⥤ Over S) (W : (D.obj (op (⊥ : Λ))).left.Opens)
    (c : Cone D) (l : Λᵒᵖ) :
    (overOpenCone D W c).π.app l ≫ overOpenι (D.obj l) (overOpenAt D W l.unop)
      = overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W) ≫ c.π.app l := by
  refine Over.OverMorphism.ext ?_
  simp only [Over.comp_left, overOpenι_left, overOpenCone]
  exact Scheme.Hom.resLE_comp_ι _ _

variable [IsDirectedOrder Λ]

/-- **The open subobjects of an inverse limit.** For an inverse system of affine objects of
`Sch/S` indexed by the opposite of a directed poset with a least element, and an open `W`
of the least stage, the open subobject of the limit over the inverse image of `W` is the limit of
the open subobjects `overOpenAt D W l` of the stages. -/
noncomputable def isLimitOverOpenCone (D : Λᵒᵖ ⥤ Over S)
    (hDaff : ∀ l, IsAffine (D.obj l).left) (W : (D.obj (op (⊥ : Λ))).left.Opens)
    (c : Cone D) (hc : IsLimit c) : IsLimit (overOpenCone D W c) := by
  have hDa : ∀ l, IsAffine ((D ⋙ Over.forget S).obj l) := hDaff
  have hAffHom : ∀ {i j : Λᵒᵖ} (f : i ⟶ j), IsAffineHom ((D ⋙ Over.forget S).map f) := by
    intro i j f
    have := hDa i
    have := hDa j
    exact isAffineHom_of_isAffine _
  have hcsch : IsLimit ((Over.forget S).mapCone c) := isLimitOfPreserves (Over.forget S) hc
  have := initial_botToOver Λ
  have hlim := (Functor.Initial.isLimitWhiskerEquiv (botToOver Λ)
      (opensCone (D ⋙ Over.forget S) ((Over.forget S).mapCone c) (op (⊥ : Λ)) W)).symm
    (isLimitOpensCone (D ⋙ Over.forget S) ((Over.forget S).mapCone c) hcsch (op (⊥ : Λ)) W)
  exact Over.isLimitLiftCone _ (overOpenAtToBase D W) _ _ (overOpenCone_w D W c) hlim

omit [IsDirectedOrder Λ] in
/-- Every stage of the inverse system of open subobjects over an affine open of the least stage
is an affine object of `Sch/S` lying over an affine open of `S`. -/
lemma isAffineOverAffineOpen_overOpenDiagram_obj (D : Λᵒᵖ ⥤ Over S)
    (hDaff : ∀ l, IsAffine (D.obj l).left) {W : (D.obj (op (⊥ : Λ))).left.Opens}
    (hW : IsAffineOpen W) (hWover : IsAffineOverAffineOpen (overOpen (D.obj (op (⊥ : Λ))) W))
    (l : Λᵒᵖ) : IsAffineOverAffineOpen ((overOpenDiagram D W).obj l) := by
  have hl := hDaff l
  have hb := hDaff (op (⊥ : Λ))
  have : IsAffineHom (D.map (homOfLE (bot_le : (⊥ : Λ) ≤ l.unop)).op).left :=
    isAffineHom_of_isAffine _
  have hopen : IsAffineOpen (overOpenAt D W l.unop) := hW.preimage _
  refine isAffineOverAffineOpen_of_hom
    (overOpenResLE (D.map (homOfLE (bot_le : (⊥ : Λ) ≤ l.unop)).op)
      (le_of_eq (rfl : overOpenAt D W l.unop
        = (D.map (homOfLE (bot_le : (⊥ : Λ) ≤ l.unop)).op).left ⁻¹ᵁ W)))
    hWover hopen

end OverOpenDiagram

/-! ### Filtered colimits along the opposite of a directed poset -/

section OpColimit

variable {Λ : Type u} [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ] {C : Type*} [Category C]
  (G : Cᵒᵖ ⥤ Type v) (E : Λᵒᵖ ⥤ C) (t : Cone E)

omit [Nonempty Λ] [IsDirectedOrder Λ] in
/-- An element of the value of a functor at the limit of an inverse system which the functor
turns into a filtered colimit comes from a stage of the system. -/
lemma exists_map_eq_of_isColimit_op (ht : IsColimit (G.mapCocone t.op)) (x : G.obj (op t.pt)) :
    ∃ (l : Λ) (y : G.obj (op (E.obj (op l)))), G.map (t.π.app (op l)).op y = x := by
  obtain ⟨l, y, hy⟩ := Types.jointly_surjective_of_isColimit ht x
  exact ⟨l.unop.unop, y, hy⟩

/-- Two elements of the value of a functor at a stage of an inverse system with the same image at
the limit, the functor turning the limit into a filtered colimit, already have the same image at
a later stage. -/
lemma exists_le_map_eq_of_isColimit_op (ht : IsColimit (G.mapCocone t.op)) {l : Λ}
    (y y' : G.obj (op (E.obj (op l))))
    (h : G.map (t.π.app (op l)).op y = G.map (t.π.app (op l)).op y') :
    ∃ (m : Λ) (hm : l ≤ m), G.map (E.map (homOfLE hm).op).op y
      = G.map (E.map (homOfLE hm).op).op y' := by
  obtain ⟨j, φ, hφ⟩ := (Types.FilteredColimit.isColimit_eq_iff' ht (i := op (op l)) y y').1 h
  refine ⟨j.unop.unop, leOfHom φ.unop.unop, ?_⟩
  have he : (homOfLE (leOfHom φ.unop.unop) : l ⟶ j.unop.unop) = φ.unop.unop :=
    Subsingleton.elim _ _
  rw [he]
  exact hφ

/-- **Recognizing that a functor turns an inverse limit into a filtered colimit.** It suffices
that every element over the limit come from a stage and that two elements over a stage with the
same image over the limit agree at a later stage. -/
lemma nonempty_isColimit_op_of_exists
    (hsurj : ∀ x : G.obj (op t.pt), ∃ (l : Λ) (y : G.obj (op (E.obj (op l)))),
      G.map (t.π.app (op l)).op y = x)
    (hinj : ∀ (l : Λ) (y y' : G.obj (op (E.obj (op l)))),
      G.map (t.π.app (op l)).op y = G.map (t.π.app (op l)).op y' →
        ∃ (m : Λ) (hm : l ≤ m), G.map (E.map (homOfLE hm).op).op y
          = G.map (E.map (homOfLE hm).op).op y') :
    Nonempty (IsColimit (G.mapCocone t.op)) := by
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y h => ?_)⟩
  · obtain ⟨l, y, hy⟩ := hsurj x
    exact ⟨op (op l), y, hy.symm⟩
  · obtain ⟨m, hm, hmeq⟩ := hinj i.unop.unop x y h
    exact ⟨op (op m), (homOfLE hm).op.op, hmeq⟩

end OpColimit

end AlgebraicGeometry.ExtendingFunctors

end
