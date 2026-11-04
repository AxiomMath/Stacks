module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelationSheaves
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackRelationSheaf
public import StacksFrontier.CategoryTheory.Sites.Topos.TypeSheafSections

/-! # The sections of the sheaf of relations are the relation data

Let `(C, J, O)` be a ringed site and `F` a sheaf of `O`-modules.  There are two descriptions of
an `n`-term relation `∑ᵢ aᵢ • sᵢ = 0` among sections of `F` in the tree:

* a *concrete* one, `Stacks.SheafOfModules.RelationData O F U n`, a structure carrying `n`
  sections of the structure sheaf, `n` sections of `F` and the vanishing of the contraction,
  assembled into the presheaf of sets `Stacks.SheafOfModules.relationPresheaf O F n`;
* a *limit-theoretic* one, `Stacks.Sheaves.RelationSheaf.relationSheaf`, the equalizer of the
  contraction morphism `∑ᵢ aᵢ • sᵢ` of generalized elements and the zero morphism out of the
  sheaf of sets `Oⁿ ⨯ Fⁿ`.

The first is what the local equational criterion for flatness is stated against; the second is
what an exact inverse image carries to the corresponding object for the inverse-image sheaf of
rings and module.  This file identifies them: the sections of the sheaf of relations over `X`
are the relation data over `X`, naturally in `X`.

## Main definitions

* `Stacks.Sheaves.RelationSheaf.ambientMk`: the section of `Oⁿ ⨯ Fⁿ` with prescribed
  coefficients and elements.
* `Stacks.Sheaves.RelationSheaf.relationSheafSectionsEquiv`: the bijection between the sections
  over `X` of the sheaf of `n`-term relations and the `n`-term relation data over `X`.
* `Stacks.Sheaves.RelationSheaf.relationSheafIso`: the same bijection as an isomorphism of
  presheaves of types.

## Main results

* `Stacks.Sheaves.RelationSheaf.relationSheafIso_hom_app_coeffs` and
  `relationSheafIso_hom_app_elts`: the coefficients and the elements of the relation attached to
  a section of the sheaf of relations are the images of the underlying section of `Oⁿ ⨯ Fⁿ`
  under the coefficient and element projections.  These are the computation rules a consumer
  needs, since the two further descriptions of `relationSheaf` available — its equalizer
  presentation and its inverse image — both speak about the underlying section of `Oⁿ ⨯ Fⁿ`.

## Implementation notes

**The scalar actions on the two sides are the same instance, not merely isomorphic.**  The
`relation` field of `Stacks.SheafOfModules.RelationData` uses the `Module` structure on
`F.val.obj X` over `(Stacks.commRingSheafToRingSheaf O).obj.obj X`, while
`Stacks.Sheaves.RelationSheaf.relationContract` is evaluated through
`CategoryTheory.Sheaf.moduleSectionsModule`.  The latter is defined as `inferInstanceAs` of the
former, so the two contraction statements are literally the same proposition and no bridging
lemma appears below; this was checked before anything here was written.

**The element calculus is used rather than the subtype description alone.**  Sections of the
equalizer are described by `Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv` as a subtype of the
sections of `Oⁿ ⨯ Fⁿ`, which is not yet a pair of families: that last step is the finite-product
element calculus `CategoryTheory.Functor.prodObjMk` and `piObjMk`, which applies because the
sections functor preserves finite products.  `Stacks.Sheaves.RelationSheaf.ambientMk` packages
the composite, and `ambient_ext` is the extensionality principle it comes with.

**Naturality is proved through `CategoryTheory.Sheaf.sectionsRestrict`.**  Restriction of
sections is a natural transformation between sections functors, so
`CategoryTheory.Functor.natTrans_app_map_apply` turns the naturality of the coefficient and
element projections into the two pointwise restriction statements, which is exactly the shape
`Stacks.SheafOfModules.relationRestrict` is defined at.

**No tag is placed in this file.**  Nothing here is a statement of the Stacks project: it is a
comparison of two of the library's own presentations of the same first-order condition.

## References

* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf CategoryTheory.Functor

universe w v u

namespace Stacks.Sheaves.RelationSheaf

/-! ### The element calculus of the ambient product -/

section Ambient

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w} R) (n : ℕ) (X : Cᵒᵖ)

/-- The section of `Rⁿ ⨯ Mⁿ` over `X` with prescribed coefficients and elements.  The sections
functor preserves finite products, so this is a bijection onto the sections of the product; the
two halves of the bijection are `map_relationCoeff_ambientMk` and `map_relationElt_ambientMk`
together with `ambient_ext`. -/
def ambientMk (a : Fin n → (sectionsFunctor J X).obj (ringSheaf R))
    (s : Fin n → (sectionsFunctor J X).obj (moduleSheaf R M)) :
    (sectionsFunctor J X).obj (relationAmbient R M n) :=
  prodObjMk (P := sectionsFunctor.{w} J X)
    (A := ∏ᶜ fun _ : Fin n => ringSheaf R) (B := ∏ᶜ fun _ : Fin n => moduleSheaf R M)
    (piObjMk (P := sectionsFunctor.{w} J X) (A := fun _ : Fin n => ringSheaf R) a)
    (piObjMk (P := sectionsFunctor.{w} J X) (A := fun _ : Fin n => moduleSheaf R M) s)

/-- The `i`-th coefficient of `ambientMk a s` is `a i`. -/
@[simp]
lemma map_relationCoeff_ambientMk (a : Fin n → (sectionsFunctor J X).obj (ringSheaf R))
    (s : Fin n → (sectionsFunctor J X).obj (moduleSheaf R M)) (i : Fin n) :
    (sectionsFunctor J X).map (relationCoeff R M n i) (ambientMk R M n X a s) = a i := by
  rw [relationCoeff, Functor.map_comp_apply, ambientMk, map_fst_prodObjMk, map_piπ_piObjMk]

/-- The `i`-th element of `ambientMk a s` is `s i`. -/
@[simp]
lemma map_relationElt_ambientMk (a : Fin n → (sectionsFunctor J X).obj (ringSheaf R))
    (s : Fin n → (sectionsFunctor J X).obj (moduleSheaf R M)) (i : Fin n) :
    (sectionsFunctor J X).map (relationElt R M n i) (ambientMk R M n X a s) = s i := by
  rw [relationElt, Functor.map_comp_apply, ambientMk, map_snd_prodObjMk, map_piπ_piObjMk]

/-- Two sections of `Rⁿ ⨯ Mⁿ` with the same coefficients and the same elements agree. -/
lemma ambient_ext {p q : (sectionsFunctor J X).obj (relationAmbient R M n)}
    (hc : ∀ i : Fin n, (sectionsFunctor J X).map (relationCoeff R M n i) p =
      (sectionsFunctor J X).map (relationCoeff R M n i) q)
    (he : ∀ i : Fin n, (sectionsFunctor J X).map (relationElt R M n i) p =
      (sectionsFunctor J X).map (relationElt R M n i) q) :
    p = q := by
  refine prodObjMk_ext (piObjMk_ext fun i => ?_) (piObjMk_ext fun i => ?_)
  · have h := hc i
    rw [relationCoeff, Functor.map_comp_apply, Functor.map_comp_apply] at h
    exact h
  · have h := he i
    rw [relationElt, Functor.map_comp_apply, Functor.map_comp_apply] at h
    exact h

/-- Every section of `Rⁿ ⨯ Mⁿ` is `ambientMk` of its coefficients and its elements. -/
@[simp]
lemma ambientMk_map_relationCoeff_map_relationElt
    (p : (sectionsFunctor J X).obj (relationAmbient R M n)) :
    ambientMk R M n X (fun i => (sectionsFunctor J X).map (relationCoeff R M n i) p)
        (fun i => (sectionsFunctor J X).map (relationElt R M n i) p) = p :=
  ambient_ext R M n X (fun i => map_relationCoeff_ambientMk R M n X _ _ i)
    (fun i => map_relationElt_ambientMk R M n X _ _ i)

/-- The contraction of `ambientMk a s` is `∑ᵢ aᵢ • sᵢ`. -/
lemma map_relationContract_ambientMk (a : Fin n → (sectionsFunctor J X).obj (ringSheaf R))
    (s : Fin n → (sectionsFunctor J X).obj (moduleSheaf R M)) :
    (sectionsFunctor J X).map (relationContract R M n) (ambientMk R M n X a s) =
      ∑ i : Fin n, a i • s i := by
  rw [sections_relationContract]
  exact Finset.sum_congr rfl fun i _ => by
    rw [map_relationCoeff_ambientMk, map_relationElt_ambientMk]

/-- The coefficients and the elements of a section of the sheaf of `n`-term relations do satisfy
the relation.  This is the equalizer condition, read through `sections_relationContract` and the
vanishing of the zero generalized element on sections. -/
lemma sum_smul_relationIota_eq_zero (y : (relationSheaf R M n).obj.obj X) :
    ∑ i : Fin n, (sectionsFunctor J X).map (relationCoeff R M n i)
          ((relationIota R M n).hom.app X y) •
        (sectionsFunctor J X).map (relationElt R M n i)
          ((relationIota R M n).hom.app X y) = 0 :=
  (sections_relationContract R M n X _).symm.trans
    ((Stacks.Sheaves.TypeSheaf.equalizer_ι_app_condition (relationContract R M n) 0 X y).trans
      (sectionsFunctor_map_hom_moduleZero X _))

end Ambient

/-! ### Restriction of coefficients and elements -/

section Restriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w} R) (n : ℕ)

/-- The `i`-th coefficient of the restriction of a section of `Rⁿ ⨯ Mⁿ` is the restriction of
its `i`-th coefficient. -/
lemma map_relationCoeff_obj_map {X Y : Cᵒᵖ} (g : X ⟶ Y) (i : Fin n)
    (p : (sectionsFunctor J X).obj (relationAmbient R M n)) :
    (sectionsFunctor J Y).map (relationCoeff R M n i)
        ((relationAmbient R M n).obj.map g p) =
      (R.obj.map g).hom ((sectionsFunctor J X).map (relationCoeff R M n i) p) :=
  (natTrans_app_map_apply (P := sectionsFunctor J X) (Q := sectionsFunctor J Y)
    (sectionsRestrict g) (relationCoeff R M n i) p).symm

/-- The `i`-th element of the restriction of a section of `Rⁿ ⨯ Mⁿ` is the restriction of its
`i`-th element. -/
lemma map_relationElt_obj_map {X Y : Cᵒᵖ} (g : X ⟶ Y) (i : Fin n)
    (p : (sectionsFunctor J X).obj (relationAmbient R M n)) :
    (sectionsFunctor J Y).map (relationElt R M n i)
        ((relationAmbient R M n).obj.map g p) =
      (M.val.map g).hom ((sectionsFunctor J X).map (relationElt R M n i) p) :=
  (natTrans_app_map_apply (P := sectionsFunctor J X) (Q := sectionsFunctor J Y)
    (sectionsRestrict g) (relationElt R M n i) p).symm

/-- The underlying section of `Rⁿ ⨯ Mⁿ` of the restriction of a section of the sheaf of
relations is the restriction of its underlying section.  This is the naturality of
`relationIota`. -/
lemma relationIota_app_obj_map {X Y : Cᵒᵖ} (g : X ⟶ Y) (y : (relationSheaf R M n).obj.obj X) :
    (relationIota R M n).hom.app Y ((relationSheaf R M n).obj.map g y) =
      (relationAmbient R M n).obj.map g ((relationIota R M n).hom.app X y) :=
  Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv_naturality
    (relationContract R M n) 0 X g y

end Restriction

/-! ### The sections of the sheaf of relations -/

section Comparison

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The sections over `X` of the sheaf of `n`-term relations are the `n`-term relations. -/
def relationSheafSectionsEquiv (O : Sheaf J CommRingCat.{w})
    (F : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) (n : ℕ) (X : Cᵒᵖ) :
    (Stacks.Sheaves.RelationSheaf.relationSheaf
        (Stacks.commRingSheafToRingSheaf O) F n).obj.obj X ≃
      Stacks.SheafOfModules.RelationData O F X n where
  toFun y :=
    { coeffs := fun i => (sectionsFunctor J X).map
        (relationCoeff (Stacks.commRingSheafToRingSheaf O) F n i)
        ((relationIota (Stacks.commRingSheafToRingSheaf O) F n).hom.app X y)
      elts := fun i => (sectionsFunctor J X).map
        (relationElt (Stacks.commRingSheafToRingSheaf O) F n i)
        ((relationIota (Stacks.commRingSheafToRingSheaf O) F n).hom.app X y)
      relation := sum_smul_relationIota_eq_zero (Stacks.commRingSheafToRingSheaf O) F n X y }
  invFun p :=
    (Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv
        (relationContract (Stacks.commRingSheafToRingSheaf O) F n) 0 X).symm
      ⟨ambientMk (Stacks.commRingSheafToRingSheaf O) F n X p.coeffs p.elts,
        (map_relationContract_ambientMk (Stacks.commRingSheafToRingSheaf O) F n X
            p.coeffs p.elts).trans
          (p.relation.trans (sectionsFunctor_map_hom_moduleZero X _).symm)⟩
  left_inv y :=
    (Equiv.symm_apply_eq _).2 (Subtype.ext
      (ambientMk_map_relationCoeff_map_relationElt
        (Stacks.commRingSheafToRingSheaf O) F n X
        ((relationIota (Stacks.commRingSheafToRingSheaf O) F n).hom.app X y)))
  right_inv p := by
    refine Stacks.SheafOfModules.RelationData.ext (funext fun i => ?_) (funext fun i => ?_)
    · refine (congrArg (fun z => (sectionsFunctor J X).map
          (relationCoeff (Stacks.commRingSheafToRingSheaf O) F n i) z)
        (Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv_symm_apply
          (relationContract (Stacks.commRingSheafToRingSheaf O) F n) 0 X _)).trans ?_
      exact map_relationCoeff_ambientMk (Stacks.commRingSheafToRingSheaf O) F n X _ _ i
    · refine (congrArg (fun z => (sectionsFunctor J X).map
          (relationElt (Stacks.commRingSheafToRingSheaf O) F n i) z)
        (Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv_symm_apply
          (relationContract (Stacks.commRingSheafToRingSheaf O) F n) 0 X _)).trans ?_
      exact map_relationElt_ambientMk (Stacks.commRingSheafToRingSheaf O) F n X _ _ i

variable (O : Sheaf J CommRingCat.{w})
  (F : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) (n : ℕ)

/-- The coefficients of the relation attached to a section of the sheaf of `n`-term relations
are the images of its underlying section of `Oⁿ ⨯ Fⁿ` under the coefficient projections. -/
@[simp]
lemma relationSheafSectionsEquiv_coeffs (X : Cᵒᵖ)
    (y : (relationSheaf (Stacks.commRingSheafToRingSheaf O) F n).obj.obj X) (i : Fin n) :
    (relationSheafSectionsEquiv O F n X y).coeffs i =
      (sectionsFunctor J X).map (relationCoeff (Stacks.commRingSheafToRingSheaf O) F n i)
        ((relationIota (Stacks.commRingSheafToRingSheaf O) F n).hom.app X y) :=
  rfl

/-- The elements of the relation attached to a section of the sheaf of `n`-term relations are
the images of its underlying section of `Oⁿ ⨯ Fⁿ` under the element projections. -/
@[simp]
lemma relationSheafSectionsEquiv_elts (X : Cᵒᵖ)
    (y : (relationSheaf (Stacks.commRingSheafToRingSheaf O) F n).obj.obj X) (i : Fin n) :
    (relationSheafSectionsEquiv O F n X y).elts i =
      (sectionsFunctor J X).map (relationElt (Stacks.commRingSheafToRingSheaf O) F n i)
        ((relationIota (Stacks.commRingSheafToRingSheaf O) F n).hom.app X y) :=
  rfl

/-- The underlying section of `Oⁿ ⨯ Fⁿ` of the section of the sheaf of relations attached to a
relation is `ambientMk` of its coefficients and its elements. -/
@[simp]
lemma relationIota_app_relationSheafSectionsEquiv_symm (X : Cᵒᵖ)
    (p : Stacks.SheafOfModules.RelationData O F X n) :
    (relationIota (Stacks.commRingSheafToRingSheaf O) F n).hom.app X
        ((relationSheafSectionsEquiv O F n X).symm p) =
      ambientMk (Stacks.commRingSheafToRingSheaf O) F n X p.coeffs p.elts :=
  Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv_symm_apply
    (relationContract (Stacks.commRingSheafToRingSheaf O) F n) 0 X _

/-- The identification of the sections of the sheaf of `n`-term relations with the `n`-term
relations is natural in the object: an isomorphism of presheaves of types between the sheaf of
`n`-term relations and `Stacks.SheafOfModules.relationPresheaf`. -/
def relationSheafIso :
    (Stacks.Sheaves.RelationSheaf.relationSheaf
        (Stacks.commRingSheafToRingSheaf O) F n).obj ≅
      Stacks.SheafOfModules.relationPresheaf O F n :=
  NatIso.ofComponents (fun X => (relationSheafSectionsEquiv O F n X).toIso) (by
    intro X Y g
    apply TypeCat.homEquiv.injective
    funext y
    change relationSheafSectionsEquiv O F n Y
        ((relationSheaf (Stacks.commRingSheafToRingSheaf O) F n).obj.map g y) =
      Stacks.SheafOfModules.relationRestrict O F g (relationSheafSectionsEquiv O F n X y)
    refine Stacks.SheafOfModules.RelationData.ext (funext fun i => ?_) (funext fun i => ?_)
    · refine (congrArg (fun z => (sectionsFunctor J Y).map
          (relationCoeff (Stacks.commRingSheafToRingSheaf O) F n i) z)
        (relationIota_app_obj_map (Stacks.commRingSheafToRingSheaf O) F n g y)).trans ?_
      exact map_relationCoeff_obj_map (Stacks.commRingSheafToRingSheaf O) F n g i _
    · refine (congrArg (fun z => (sectionsFunctor J Y).map
          (relationElt (Stacks.commRingSheafToRingSheaf O) F n i) z)
        (relationIota_app_obj_map (Stacks.commRingSheafToRingSheaf O) F n g y)).trans ?_
      exact map_relationElt_obj_map (Stacks.commRingSheafToRingSheaf O) F n g i _)

/-- The coefficients of the relation `relationSheafIso` attaches to a section of the sheaf of
`n`-term relations: the `i`-th coefficient of the underlying section of `Oⁿ ⨯ Fⁿ`. -/
lemma relationSheafIso_hom_app_coeffs (X : Cᵒᵖ)
    (y : (relationSheaf (Stacks.commRingSheafToRingSheaf O) F n).obj.obj X) (i : Fin n) :
    (((relationSheafIso O F n).hom.app X) y).coeffs i =
      (sectionsFunctor J X).map (relationCoeff (Stacks.commRingSheafToRingSheaf O) F n i)
        ((relationIota (Stacks.commRingSheafToRingSheaf O) F n).hom.app X y) :=
  rfl

/-- The elements of the relation `relationSheafIso` attaches to a section of the sheaf of
`n`-term relations: the `i`-th element of the underlying section of `Oⁿ ⨯ Fⁿ`. -/
lemma relationSheafIso_hom_app_elts (X : Cᵒᵖ)
    (y : (relationSheaf (Stacks.commRingSheafToRingSheaf O) F n).obj.obj X) (i : Fin n) :
    (((relationSheafIso O F n).hom.app X) y).elts i =
      (sectionsFunctor J X).map (relationElt (Stacks.commRingSheafToRingSheaf O) F n i)
        ((relationIota (Stacks.commRingSheafToRingSheaf O) F n).hom.app X y) :=
  rfl

/-- The underlying section of `Oⁿ ⨯ Fⁿ` of the section of the sheaf of relations that
`relationSheafIso` attaches to a relation. -/
lemma relationIota_app_relationSheafIso_inv_app (X : Cᵒᵖ)
    (p : Stacks.SheafOfModules.RelationData O F X n) :
    (relationIota (Stacks.commRingSheafToRingSheaf O) F n).hom.app X
        (((relationSheafIso O F n).inv.app X) p) =
      ambientMk (Stacks.commRingSheafToRingSheaf O) F n X p.coeffs p.elts :=
  relationIota_app_relationSheafSectionsEquiv_symm O F n X p

end Comparison

end Stacks.Sheaves.RelationSheaf

end
