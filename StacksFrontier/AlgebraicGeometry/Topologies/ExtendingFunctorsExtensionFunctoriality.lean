module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsLimits

/-!
# Functoriality of the extension of a functor on a full subcategory of schemes over a base

Let `S` be a scheme and let `𝒞` be a full subcategory of `Sch/S`. The extension
`AlgebraicGeometry.ExtendingFunctors.extension` of a functor on `𝒞` to `Sch/S` is built from two
Kan extensions, and both halves are functorial in the functor being extended: a morphism
`σ : F₁ ⟶ F₂` of functors on `𝒞` induces a morphism `extension P F₁ ⟶ extension P F₂` of their
extensions. This file constructs that morphism and proves the one property of it which the
uniqueness statement of Stacks 0EUW does not record: it is compatible with the identification
`AlgebraicGeometry.ExtendingFunctors.restrictionHom` of the restriction of the extension with the
functor being extended.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.affineExtensionMap`: the morphism of colimit formulas
  induced by a morphism of functors on the subcategory.
* `AlgebraicGeometry.ExtendingFunctors.extensionMap`: the morphism of extensions induced by a
  morphism of functors on the subcategory.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.whiskerLeft_extensionMap_comp_restrictionHom`: the
  canonical map from the restriction of the extension to the functor being extended is natural in
  that functor.
* `AlgebraicGeometry.ExtendingFunctors.isIso_restrictionHom`: that canonical map is an
  isomorphism, which is the sharp form of
  `AlgebraicGeometry.ExtendingFunctors.nonempty_restrictionIso`.

## Implementation notes

The colimit half is the left Kan extension along the inclusion of the part of the subcategory
which is locally of finite presentation over `S`, so the induced map is obtained from
`CategoryTheory.Functor.descOfIsLeftKanExtension`; it is computed on the legs
`AlgebraicGeometry.ExtendingFunctors.affineExtensionι` of the colimit by
`AlgebraicGeometry.ExtendingFunctors.affineExtensionMap_affineExtensionι`.

The limit half is not obtained from `CategoryTheory.Functor.liftOfIsRightKanExtension` but
pointwise from `AlgebraicGeometry.ExtendingFunctors.extensionMk`, which makes the projections
`AlgebraicGeometry.ExtendingFunctors.extensionπ` of the induced map computable by definition and
so avoids a second appeal to the universal property.

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u

variable {S : Scheme.{u}} {P : ObjectProperty (Over S)}
  {F₁ F₂ : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))}

/-! ### The colimit formula is a left Kan extension -/

/-- The colimit formula is the left Kan extension of the restriction of `F` to the part of the
subcategory which is locally of finite presentation over `S`, stated for
`AlgebraicGeometry.ExtendingFunctors.affineExtension` and its unit rather than for the
`CategoryTheory.Functor.pointwiseLeftKanExtension` they are defined to be. -/
instance isLeftKanExtension_affineExtension (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) :
    (affineExtension P F).IsLeftKanExtension (affineExtensionUnit P F) :=
  inferInstanceAs ((Functor.pointwiseLeftKanExtension (lfpPart P).ι.op
    (lfpRestriction P F)).IsLeftKanExtension (Functor.pointwiseLeftKanExtensionUnit _ _))

/-! ### The morphism of colimit formulas induced by a morphism of functors -/

/-- The restriction to the part of the subcategory which is locally of finite presentation over
`S` of a morphism of functors on the subcategory. This is `CategoryTheory.Functor.whiskerLeft`
along the inclusion, named so that its values carry the type
`AlgebraicGeometry.ExtendingFunctors.lfpRestriction` rather than the composition it unfolds to. -/
def lfpRestrictionMap (σ : F₁ ⟶ F₂) : lfpRestriction P F₁ ⟶ lfpRestriction P F₂ :=
  Functor.whiskerLeft (lfpIncl P).op σ

/-- **The colimit formula is functorial.** A morphism `F₁ ⟶ F₂` of functors on the subcategory
induces a morphism `colim_{Y → V'} F₁(V') ⟶ colim_{Y → V'} F₂(V')` of the colimit formulas. -/
noncomputable def affineExtensionMap (σ : F₁ ⟶ F₂) :
    affineExtension P F₁ ⟶ affineExtension P F₂ :=
  (affineExtension P F₁).descOfIsLeftKanExtension (affineExtensionUnit P F₁)
    (affineExtension P F₂) (lfpRestrictionMap σ ≫ affineExtensionUnit P F₂)

/-- The restriction of a morphism of functors to the locally-finitely-presented part is computed
by the morphism itself. -/
lemma lfpRestrictionMap_apply (σ : F₁ ⟶ F₂) (Z : P.FullSubcategory)
    (A : (lfpPart P).FullSubcategory) (g : Z ⟶ (lfpIncl P).obj A)
    (y : (lfpRestriction P F₁).obj (op A)) :
    F₂.map g.op ((lfpRestrictionMap σ).app (op A) y) = σ.app (op Z) (F₁.map g.op y) :=
  (NatTrans.naturality_apply σ g.op y).symm

/-- The induced morphism of colimit formulas on the leg at an arrow into an object of the
subcategory which is locally of finite presentation over `S`. -/
lemma affineExtensionMap_affineExtensionι (σ : F₁ ⟶ F₂) {Y : Over S}
    (A : (lfpPart P).FullSubcategory) (f : Y ⟶ A.obj)
    (y : (lfpRestriction P F₁).obj (op A)) :
    (affineExtensionMap σ).app (op Y) (affineExtensionι P F₁ A f y)
      = affineExtensionι P F₂ A f ((lfpRestrictionMap σ).app (op A) y) := by
  have h := ConcreteCategory.congr_hom (Functor.descOfIsLeftKanExtension_fac_app
    (affineExtension P F₁) (affineExtensionUnit P F₁) (affineExtension P F₂)
    (lfpRestrictionMap σ ≫ affineExtensionUnit P F₂) (op A)) y
  rw [CategoryTheory.comp_apply, NatTrans.comp_app, CategoryTheory.comp_apply] at h
  have hfac : (affineExtensionMap σ).app (op A.obj) (affineExtensionι P F₁ A (𝟙 A.obj) y)
      = affineExtensionι P F₂ A (𝟙 A.obj) ((lfpRestrictionMap σ).app (op A) y) := h
  have key : ∀ (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
      (z : (lfpRestriction P F).obj (op A)), affineExtensionι P F A f z
        = (affineExtension P F).map f.op (affineExtensionι P F A (𝟙 A.obj) z) := fun F z => by
    rw [affineExtensionι_naturality, Category.comp_id]
  rw [key F₁ y, key F₂, ← hfac]
  exact NatTrans.naturality_apply (affineExtensionMap σ) f.op _

/-- The induced morphism of colimit formulas is compatible with the comparison of the colimit
formula with the functor being extended. -/
lemma affineExtensionToF_affineExtensionMap (σ : F₁ ⟶ F₂) (Z : P.FullSubcategory)
    (x : (affineExtension P F₁).obj (op Z.obj)) :
    affineExtensionToF F₂ Z ((affineExtensionMap σ).app (op Z.obj) x)
      = σ.app (op Z) (affineExtensionToF F₁ Z x) := by
  obtain ⟨A, f, y, rfl⟩ := exists_affineExtensionι_eq_of_arrow F₁ Z.obj x
  rw [affineExtensionMap_affineExtensionι, affineExtensionToF_affineExtensionι,
    affineExtensionToF_affineExtensionι]
  exact lfpRestrictionMap_apply σ Z A (ObjectProperty.homMk f) y

/-! ### The morphism of extensions induced by a morphism of functors -/

/-- The family of sections of the colimit formula for `F₂` attached to a section of the extension
of `F₁`: the projections of the limit computing the extension, moved by the induced morphism of
colimit formulas. -/
noncomputable def extensionMapFamily (σ : F₁ ⟶ F₂) {X : Over S}
    (t : (extension P F₁).obj (op X)) (V : Over S) (hV : IsAffineOverAffineOpen V) (f : V ⟶ X) :
    (affineExtension P F₂).obj (op V) :=
  (affineExtensionMap σ).app (op V) (extensionπ P F₁ hV f t)

/-- The family of sections of the colimit formula moved by the induced morphism is compatible, so
defines a section of the extension of `F₂`. -/
lemma extensionMapFamily_compatible (σ : F₁ ⟶ F₂) {X : Over S}
    (t : (extension P F₁).obj (op X)) (V V' : Over S) (hV : IsAffineOverAffineOpen V)
    (hV' : IsAffineOverAffineOpen V') (f : V ⟶ X) (k : V' ⟶ V) :
    (affineExtension P F₂).map k.op (extensionMapFamily σ t V hV f)
      = extensionMapFamily σ t V' hV' (k ≫ f) := by
  show (affineExtension P F₂).map k.op
      ((affineExtensionMap σ).app (op V) (extensionπ P F₁ hV f t))
    = (affineExtensionMap σ).app (op V') (extensionπ P F₁ hV' (k ≫ f) t)
  rw [← extensionπ_map P F₁ hV hV' k f t]
  exact (NatTrans.naturality_apply (affineExtensionMap σ) k.op
    (extensionπ P F₁ hV f t)).symm

/-- The value at an object of `Sch/S` of the morphism of extensions induced by a morphism of
functors on the subcategory. -/
noncomputable def extensionMapApp (σ : F₁ ⟶ F₂) {X : Over S}
    (t : (extension P F₁).obj (op X)) : (extension P F₂).obj (op X) :=
  extensionMk P F₂ (extensionMapFamily σ t) (extensionMapFamily_compatible σ t)

/-- The projections of `extensionMapApp σ t` are the projections of `t` moved by the induced
morphism of colimit formulas. -/
@[simp]
lemma extensionπ_extensionMapApp (σ : F₁ ⟶ F₂) {X : Over S}
    (t : (extension P F₁).obj (op X)) {V : Over S} (hV : IsAffineOverAffineOpen V) (f : V ⟶ X) :
    extensionπ P F₂ hV f (extensionMapApp σ t)
      = (affineExtensionMap σ).app (op V) (extensionπ P F₁ hV f t) :=
  extensionπ_extensionMk P F₂ (extensionMapFamily σ t) (extensionMapFamily_compatible σ t) hV f

/-- **The extension is functorial.** A morphism `F₁ ⟶ F₂` of functors on the subcategory induces
a morphism `extension P F₁ ⟶ extension P F₂` of their extensions to `Sch/S`. -/
noncomputable def extensionMap (σ : F₁ ⟶ F₂) : extension P F₁ ⟶ extension P F₂ where
  app X := TypeCat.ofHom (extensionMapApp σ (X := X.unop))
  naturality X X' g := by
    ext t
    change extensionMapApp σ ((extension P F₁).map g.unop.op t)
      = (extension P F₂).map g.unop.op (extensionMapApp σ t)
    refine extension_ext P F₂ _ _ fun V hV f => ?_
    rw [extensionπ_extensionMapApp, extensionπ_naturality, extensionπ_naturality,
      extensionπ_extensionMapApp]

/-- The projections of the image of a section under the induced morphism of extensions are the
projections of the section moved by the induced morphism of colimit formulas. -/
@[simp]
lemma extensionπ_extensionMap (σ : F₁ ⟶ F₂) {X : Over S}
    (t : (extension P F₁).obj (op X)) {V : Over S} (hV : IsAffineOverAffineOpen V) (f : V ⟶ X) :
    extensionπ P F₂ hV f ((extensionMap σ).app (op X) t)
      = (affineExtensionMap σ).app (op V) (extensionπ P F₁ hV f t) :=
  extensionπ_extensionMapApp σ t hV f

/-! ### Naturality of the identification of the restriction of the extension -/

/-- The induced morphism of extensions is compatible, pointwise, with the identification of the
restriction of the extension with the functor being extended. -/
theorem restrictionApp_extensionMap (hP1 : HasAffineOpens P)
    (ha₁ : IsZariskiSheafOnSubcategory P F₁) (ha₂ : IsZariskiSheafOnSubcategory P F₂)
    (σ : F₁ ⟶ F₂) (Z : P.FullSubcategory) (t : (extension P F₁).obj (op Z.obj)) :
    restrictionApp F₂ hP1 ha₂ Z ((extensionMap σ).app (op Z.obj) t)
      = σ.app (op Z) (restrictionApp F₁ hP1 ha₁ Z t) := by
  refine (restrictionApp_unique F₂ hP1 ha₂ Z _ _ fun B hB g => ?_).symm
  calc F₂.map g.op (σ.app (op Z) (restrictionApp F₁ hP1 ha₁ Z t))
      = σ.app (op B) (F₁.map g.op (restrictionApp F₁ hP1 ha₁ Z t)) :=
        (NatTrans.naturality_apply σ g.op (restrictionApp F₁ hP1 ha₁ Z t)).symm
    _ = σ.app (op B) (affineExtensionToF F₁ B (extensionπ P F₁ hB (P.ι.map g) t)) :=
        congrArg (fun z => σ.app (op B) z) (restrictionApp_spec F₁ hP1 ha₁ Z t B hB g)
    _ = affineExtensionToF F₂ B
          ((affineExtensionMap σ).app (op B.obj) (extensionπ P F₁ hB (P.ι.map g) t)) :=
        (affineExtensionToF_affineExtensionMap σ B (extensionπ P F₁ hB (P.ι.map g) t)).symm
    _ = affineExtensionToF F₂ B
          (extensionπ P F₂ hB (P.ι.map g) ((extensionMap σ).app (op Z.obj) t)) :=
        congrArg (fun z => affineExtensionToF F₂ B z)
          (extensionπ_extensionMap σ t hB (P.ι.map g)).symm

/-- **The identification of the restriction of the extension with the functor being extended is
natural in that functor.** -/
theorem whiskerLeft_extensionMap_comp_restrictionHom (hP1 : HasAffineOpens P)
    (ha₁ : IsZariskiSheafOnSubcategory P F₁) (ha₂ : IsZariskiSheafOnSubcategory P F₂)
    (σ : F₁ ⟶ F₂) :
    Functor.whiskerLeft P.ι.op (extensionMap σ) ≫ restrictionHom F₂ hP1 ha₂
      = restrictionHom F₁ hP1 ha₁ ≫ σ := by
  refine NatTrans.ext (funext fun Z => ?_)
  ext t
  exact restrictionApp_extensionMap hP1 ha₁ ha₂ σ Z.unop t

/-- **The restriction of the extension to the subcategory is `F`**, in the sharp form which names
the map: the canonical map `AlgebraicGeometry.ExtendingFunctors.restrictionHom` is an
isomorphism. -/
lemma isIso_restrictionHom (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (haF : IsZariskiSheafOnSubcategory P F) (hbF : PreservesAffineLimitsOnSubcategory P F) :
    IsIso (restrictionHom F hP1 haF) :=
  have : ∀ Z : P.FullSubcategoryᵒᵖ, IsIso ((restrictionHom F hP1 haF).app Z) := fun Z =>
    (isIso_iff_bijective _).2 ⟨restrictionApp_injective F hP1 hP2 haF hbF Z.unop,
      restrictionApp_surjective F hP1 hP2 haF hbF Z.unop⟩
  NatIso.isIso_of_isIso_app _

/-- **Every morphism between the restrictions of two extensions is induced by a morphism of the
extensions.** The induced morphism is the one attached to the morphism of the functors being
extended obtained by transporting along the isomorphisms
`AlgebraicGeometry.ExtendingFunctors.restrictionHom`. -/
theorem exists_whiskerLeft_eq_of_extension (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P) (ha₁ : IsZariskiSheafOnSubcategory P F₁)
    (hb₁ : PreservesAffineLimitsOnSubcategory P F₁)
    (ha₂ : IsZariskiSheafOnSubcategory P F₂)
    (hb₂ : PreservesAffineLimitsOnSubcategory P F₂)
    (σ : P.ι.op ⋙ extension P F₁ ⟶ P.ι.op ⋙ extension P F₂) :
    ∃ θ : extension P F₁ ⟶ extension P F₂, Functor.whiskerLeft P.ι.op θ = σ := by
  have h₁ : IsIso (restrictionHom F₁ hP1 ha₁) := isIso_restrictionHom F₁ hP1 hP2 ha₁ hb₁
  have h₂ : IsIso (restrictionHom F₂ hP1 ha₂) := isIso_restrictionHom F₂ hP1 hP2 ha₂ hb₂
  refine ⟨extensionMap (CategoryTheory.inv (restrictionHom F₁ hP1 ha₁) ≫ σ ≫
    restrictionHom F₂ hP1 ha₂), ?_⟩
  have hw := whiskerLeft_extensionMap_comp_restrictionHom hP1 ha₁ ha₂
    (CategoryTheory.inv (restrictionHom F₁ hP1 ha₁) ≫ σ ≫ restrictionHom F₂ hP1 ha₂)
  rw [IsIso.hom_inv_id_assoc] at hw
  exact (cancel_mono (restrictionHom F₂ hP1 ha₂)).1 hw

end AlgebraicGeometry.ExtendingFunctors

end
