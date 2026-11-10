module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctors

/-!
# Extending functors from a full subcategory of schemes, the existence of the extension

Let `S` be a scheme, let `𝒞` be a full subcategory of `Sch/S` satisfying conditions (1) and (2)
of Stacks 0EUW, and let `F : 𝒞ᵒᵖ ⥤ Set` satisfy conditions (a) and (b). The uniqueness of the
extension of `F` to `Sch/S` is proved in
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctors`. This file constructs the extension.

## The construction

Write `𝒞_lfp` for the objects of `𝒞` locally of finite presentation over `S` and `Aff` for the
objects of `Sch/S` which are affine and lie over an affine open of `S`. The extension is

`F' = Ran` along `Affᵒᵖ ↪ (Sch/S)ᵒᵖ` of the restriction to `Affᵒᵖ` of `Lan` along
`𝒞_lfpᵒᵖ ↪ (Sch/S)ᵒᵖ` of `F`,

i.e. pointwise

`F'(X) = lim_{V → X, V ∈ Aff} colim_{V → V', V' ∈ 𝒞_lfp} F(V')`.

The inner colimit is the formula `F'(V) = colim_{V → V'} F(V')` of the source, and the outer
limit is the passage from a sheaf on the basis of affine opens lying over affine opens of `S` to
a sheaf on all of `X`. Both halves are Mathlib's pointwise Kan extensions, so both have real
bodies and `F'` is a functor on all of `(Sch/S)ᵒᵖ` by construction: the source's second omitted
step, the functoriality of `F'` over `Sch/S`, needs no separate argument and in particular needs
neither Stacks 009X nor any bridge between the three incompatible sheaf-on-a-basis idioms in the
library.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.lfpPart`, `.IsAffineOverAffineOpen`: the subcategories
  `𝒞_lfp` and `Aff` above.
* `AlgebraicGeometry.ExtendingFunctors.affineExtension`: the colimit formula
  `colim_{V → V'} F(V')`, as a functor on all of `(Sch/S)ᵒᵖ`.
* `AlgebraicGeometry.ExtendingFunctors.extension`: the extension `F'`.
* `AlgebraicGeometry.ExtendingFunctors.ArrowsInto`: the index category of the colimit, the
  arrows from an object into the objects of `𝒞_lfp`.
* `AlgebraicGeometry.ExtendingFunctors.presentationArrows`: a presentation `V = lim V_l`, read
  as a diagram in that index category.
* `AlgebraicGeometry.ExtendingFunctors.subcategoryCocone`: for an object `Z` of `𝒞`, the cocone
  with apex `F(Z)` on the diagram whose colimit is `F'(Z)`.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.exists_lfpPresentation`: an object of `Aff` is a directed
  inverse limit of objects of `𝒞_lfp`.
* `AlgebraicGeometry.ExtendingFunctors.final_presentationArrows`: such a presentation is cofinal
  in `ArrowsInto`. This is the cofinality the source quotes Stacks 01ZC for; the two halves of
  the finality criterion are parts (2) and (3) of that tag.
* `AlgebraicGeometry.ExtendingFunctors.isColimitPresentationCocone`,
  `AlgebraicGeometry.ExtendingFunctors.colimitPresentationIso`: consequently the two formulas
  `F'(V) = colim_l F(V_l)` and `F'(V) = colim_{V → V'} F(V')` of the source agree.
* `AlgebraicGeometry.ExtendingFunctors.nonempty_extensionObjIso`: the value of `F'` at an affine
  object of `𝒞` lying over an affine open of `S` is the value of `F`, which is the source's
  remark that `F'(V) = F(V)` by assumption (b) when `V` is an object of `𝒞`.

## Implementation notes

The values of `F` are taken in `Type (max w (u + 1))` rather than in an arbitrary `Type w`: the
index category of the colimit has objects in `Type (u + 1)`, since `Over S` does, so the colimit
is formed in `Type (u + 1)` at the smallest. Pinning the value universe there lets the Kan
extensions be taken without any universe lift, so the extension restricts to `F` on the nose
rather than to a copy of it.

That the extension is a Zariski sheaf is proved in
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf`.

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 00QN](https://stacks.math.columbia.edu/tag/00QN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u

variable {S : Scheme.{u}}

/-- The part of a full subcategory of `Sch/S` consisting of the objects which are locally of
finite presentation over `S`. -/
def lfpPart (P : ObjectProperty (Over S)) : ObjectProperty (Over S) :=
  fun X => P X ∧ LocallyOfFinitePresentation X.hom

/-- The objects of `Sch/S` which are affine and whose structure morphism factors through an
affine open of `S`. -/
def IsAffineOverAffineOpen : ObjectProperty (Over S) :=
  fun X => IsAffine X.left ∧
    ∃ (U : S.affineOpens) (g : X.left ⟶ U.1.toScheme), g ≫ U.1.ι = X.hom

/-- The locally-finitely-presented part of `P` is contained in `P`. -/
lemma lfpPart_le (P : ObjectProperty (Over S)) : lfpPart P ≤ P := fun _ h => h.1

/-- The inclusion of the locally-finitely-presented part into the full subcategory. -/
def lfpIncl (P : ObjectProperty (Over S)) :
    (lfpPart P).FullSubcategory ⥤ P.FullSubcategory :=
  ObjectProperty.ιOfLE (lfpPart_le P)

/-- The restriction of `F` to the locally-finitely-presented part of the subcategory. -/
def lfpRestriction (P : ObjectProperty (Over S)) (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) :
    (lfpPart P).FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)) :=
  (lfpIncl P).op ⋙ F

/-- The left Kan extension of `F` along the inclusion of the locally-finitely-presented part. -/
noncomputable def affineExtension (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) : (Over S)ᵒᵖ ⥤ Type (max w (u + 1)) :=
  Functor.pointwiseLeftKanExtension (lfpPart P).ι.op (lfpRestriction P F)

/-- The extension of `F`. -/
noncomputable def extension (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) : (Over S)ᵒᵖ ⥤ Type (max w (u + 1)) :=
  Functor.pointwiseRightKanExtension (IsAffineOverAffineOpen (S := S)).ι.op
    ((IsAffineOverAffineOpen (S := S)).ι.op ⋙ affineExtension P F)

variable (P : ObjectProperty (Over S)) (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))

/-- The unit of the colimit formula: the value of `F` at an object of the subcategory which is
locally of finite presentation over `S` maps to the colimit defining `affineExtension`. -/
noncomputable def affineExtensionUnit :
    lfpRestriction P F ⟶ (lfpPart P).ι.op ⋙ affineExtension P F :=
  Functor.pointwiseLeftKanExtensionUnit _ _

/-- On the objects of the subcategory which are locally of finite presentation over `S`, the
colimit `colim_{V → V'} F(V')` is computed by the identity arrow: the arrows out of such an
object into the subcategory have a terminal one. -/
instance isIso_affineExtensionUnit : IsIso (affineExtensionUnit P F) :=
  (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _ _).isIso_hom

/-- The identification of `affineExtension P F` with `F` on the objects of the subcategory which
are locally of finite presentation over `S`. -/
noncomputable def affineExtensionIsoOnLfp :
    lfpRestriction P F ≅ (lfpPart P).ι.op ⋙ affineExtension P F :=
  asIso (affineExtensionUnit P F)

/-- The counit of the limit formula: the extension restricted to the affine objects lying over
an affine open of `S` maps to `affineExtension`. -/
noncomputable def extensionCounit :
    (IsAffineOverAffineOpen (S := S)).ι.op ⋙ extension P F ⟶
      (IsAffineOverAffineOpen (S := S)).ι.op ⋙ affineExtension P F :=
  Functor.pointwiseRightKanExtensionCounit _ _

/-- On an affine object lying over an affine open of `S`, the limit defining the extension is
computed by the identity arrow: the arrows into such an object out of the affine objects over
affine opens have an initial one. -/
instance isIso_extensionCounit : IsIso (extensionCounit P F) :=
  (Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension _ _).isIso_hom

/-- The extension agrees with the colimit formula `colim_{V → V'} F(V')` on the affine objects
of `Sch/S` whose structure morphism factors through an affine open of `S`. -/
noncomputable def extensionIsoOnAffine :
    (IsAffineOverAffineOpen (S := S)).ι.op ⋙ extension P F ≅
      (IsAffineOverAffineOpen (S := S)).ι.op ⋙ affineExtension P F :=
  asIso (extensionCounit P F)

/-! ### Presentations by objects of the subcategory -/

/-- The raw presentation: an affine object of `Sch/S` lying over an affine open of `S` is a
directed inverse limit of affine objects each isomorphic to an object of the subcategory which is
locally of finite presentation over `S`.

This refines `exists_limit_of_isAffine_over_affineOpen` by recording local finite presentation,
which holds because the approximating objects are built from morphisms of finite presentation to
an affine open of `S`. -/
theorem exists_lfp_limit_of_isAffineOverAffineOpen {P : ObjectProperty (Over S)}
    (hP : HasFinitePresentationAffines P) (X : Over S) (hX : IsAffineOverAffineOpen X) :
    ∃ (Λ : Type u) (_ : PartialOrder Λ) (_ : Nonempty Λ) (_ : IsDirectedOrder Λ)
      (D : Λᵒᵖ ⥤ Over S) (c : Cone D) (_ : IsLimit c) (_ : c.pt ≅ X),
      (∀ l, IsAffine (D.obj l).left) ∧
        ∀ l, ∃ Y : Over S, lfpPart P Y ∧ Nonempty (D.obj l ≅ Y) := by
  obtain ⟨hXaff, U, g, hg⟩ := hX
  have : IsAffine X.left := hXaff
  have hUaff : IsAffine U.1.toScheme := U.2
  obtain ⟨Λ, _, _, _, D₀, c₀, hc₀, e, b, hDaff, hbfp, hfac⟩ :=
    Stacks.AlgebraicGeometry.Tag05JXGeneral.exists_directedOrder_affine_limit_presentation g
  let t : D₀ ⟶ (Functor.const Λᵒᵖ).obj S :=
    { app l := b.app l ≫ U.1.ι
      naturality := by
        intro l m h
        have hb := b.naturality h
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hb ⊢
        rw [← Category.assoc, hb] }
  let p : c₀.pt ⟶ S := e.inv ≫ X.hom
  have hp : ∀ l, c₀.π.app l ≫ t.app l = p := by
    intro l
    have h1 : e.inv ≫ g = c₀.π.app l ≫ b.app l := by
      rw [hfac l, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    change c₀.π.app l ≫ b.app l ≫ U.1.ι = e.inv ≫ X.hom
    rw [← Category.assoc, ← h1, Category.assoc, hg]
  refine ⟨Λ, inferInstance, inferInstance, inferInstance, Over.lift D₀ t,
    Over.liftCone D₀ t c₀ p hp, Over.isLimitLiftCone D₀ t c₀ p hp hc₀,
    Over.isoMk e.symm rfl, hDaff, fun l => ?_⟩
  have hDl : IsAffine (D₀.obj l) := hDaff l
  let gl : D₀.obj l ⟶ U.1.toScheme := b.app l
  have hglaff : IsAffineHom gl := isAffineHom_of_isAffine gl
  have hbl : LocallyOfFinitePresentation gl := hbfp l
  obtain ⟨Y, hPY, ⟨i⟩⟩ := hP U (D₀.obj l) gl (hDaff l) ⟨hbfp l, inferInstance, inferInstance⟩
  refine ⟨Y, ⟨hPY, ?_⟩, ⟨i⟩⟩
  have hw : i.inv.left ≫ (Over.mk (gl ≫ U.1.ι)).hom = Y.hom := Over.w i.inv
  have hiso : IsIso i.inv.left := inferInstanceAs (IsIso ((Over.forget S).map i.inv))
  rw [← hw]
  exact inferInstanceAs (LocallyOfFinitePresentation (i.inv.left ≫ gl ≫ U.1.ι))

/-- The presentation, with the approximating objects taken inside the subcategory: an affine
object of `Sch/S` lying over an affine open of `S` is a directed inverse limit of affine objects
of the subcategory which are locally of finite presentation over `S`. -/
theorem exists_lfpPresentation {P : ObjectProperty (Over S)}
    (hP : HasFinitePresentationAffines P) (X : Over S) (hX : IsAffineOverAffineOpen X) :
    ∃ (Λ : Type u) (_ : PartialOrder Λ) (_ : Nonempty Λ) (_ : IsDirectedOrder Λ)
      (D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory) (c : Cone (D ⋙ (lfpPart P).ι)) (_ : IsLimit c)
      (_ : c.pt ≅ X), ∀ l, IsAffine (D.obj l).obj.left := by
  classical
  obtain ⟨Λ, _, _, _, D₁, c₁, hc₁, ci, hDaff, hmem⟩ :=
    exists_lfp_limit_of_isAffineOverAffineOpen hP X hX
  choose Y hY hiso using hmem
  let e : ∀ l, D₁.obj l ≅ Y l := fun l => (hiso l).some
  let α : D₁ ≅ D₁.copyObj Y e := Functor.isoCopyObj D₁ Y e
  refine ⟨Λ, inferInstance, inferInstance, inferInstance,
    (lfpPart P).lift (D₁.copyObj Y e) hY, (Cone.postcompose α.hom).obj c₁,
    (IsLimit.postcomposeHomEquiv α c₁).symm hc₁, ci, fun l => ?_⟩
  have : IsAffine (D₁.obj l).left := hDaff l
  have eiso : (Y l).left ≅ (D₁.obj l).left := ((Over.forget S).mapIso (e l)).symm
  change IsAffine (Y l).left
  exact IsAffine.of_isIso eiso.hom

/-! ### Cofinality of a presentation in the index category of the colimit -/

/-- The index category of the colimit defining the extension on the affine objects: the arrows
from `V` into the objects of the subcategory which are locally of finite presentation over `S`.
This is the category over which the colimit `colim_{V → V'} F(V')` of the source is taken. -/
abbrev ArrowsInto (P : ObjectProperty (Over S)) (V : Over S) : Type (u + 1) :=
  CostructuredArrow (lfpPart P).ι.op (op V)

section Presentation

variable {P : ObjectProperty (Over S)} {V : Over S} {Λ : Type u} [Preorder Λ]
  {D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory}

/-- The functor from the index poset of a presentation `V = lim V_l` into the index category of
the colimit, sending `l` to the projection `V ⟶ V_l`. -/
def presentationArrows (c : Cone (D ⋙ (lfpPart P).ι)) (ci : c.pt ≅ V) :
    Λ ⥤ ArrowsInto P V where
  obj l := CostructuredArrow.mk (Y := op (D.obj (op l))) ((ci.inv ≫ c.π.app (op l)).op)
  map {l m} h := CostructuredArrow.homMk (D.map h.op).op (by
    apply Quiver.Hom.unop_inj
    simpa using c.w h.op)
  map_id l := by
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    simp
  map_comp {l m n} h k := by
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    simp

variable (c : Cone (D ⋙ (lfpPart P).ι)) (ci : c.pt ≅ V)

/-- The object of the index category assigned to `l` has source `V_l`. -/
@[simp]
lemma presentationArrows_obj_left (l : Λ) :
    ((presentationArrows c ci).obj l).left = op (D.obj (op l)) :=
  rfl

/-- The arrow assigned to `l` is the projection `V ⟶ V_l` of the presentation. -/
@[simp]
lemma presentationArrows_obj_hom (l : Λ) :
    ((presentationArrows c ci).obj l).hom = (ci.inv ≫ c.π.app (op l)).op :=
  rfl

/-- The morphism assigned to `l ⟶ m` is the transition map `V_m ⟶ V_l` of the presentation. -/
@[simp]
lemma presentationArrows_map_left {l m : Λ} (h : l ⟶ m) :
    ((presentationArrows c ci).map h).left = (D.map h.op).op :=
  rfl

end Presentation

-- The cofinality argument reads a morphism of the index category of the colimit as a morphism of
-- the subcategory, which needs the functor out of the index poset to unfold at `implicit`
-- transparency.
attribute [local implicit_reducible] presentationArrows

/-- **The second half of Stacks 01ZC in the form needed for cofinality.** Two morphisms from a
member of a cofiltered inverse system of affine schemes over `S` into an object whose functor of
points is limit preserving which agree after restriction to the limit already agree after
restriction to some later member of the system. -/
theorem exists_map_comp_eq_of_isLimitPreserving {Z : Over S}
    (H : Scheme.IsLimitPreserving S (yoneda.obj Z)) {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Over S) (c : Cone D) (hc : IsLimit c) (hD : ∀ i, IsAffine (D.obj i).left)
    {i : I} (g₁ g₂ : D.obj i ⟶ Z) (h : c.π.app i ≫ g₁ = c.π.app i ≫ g₂) :
    ∃ (j : I) (φ : j ⟶ i), D.map φ ≫ g₁ = D.map φ ≫ g₂ := by
  obtain ⟨hcol⟩ := (H I D hD).preserves hc.op
  obtain ⟨j, φ, hj⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (F := D.op ⋙ yoneda.obj Z) hcol (i := op i) g₁ g₂).1 h
  exact ⟨j.unop, φ.unop, hj⟩

/-- **The cofinality asserted by Stacks 0EUW.** For an affine object `V` of `Sch/S` lying over an
affine open of `S`, a presentation `V = lim V_l` by objects of the subcategory which are locally
of finite presentation over `S` is cofinal in the category of all arrows from `V` into such
objects.

This is the statement of the source that "by Limits, Proposition 01ZC our inverse system `V_i` is
cofinal in this category", which is what makes the two formulas
`F'(V) = colim F(V_i)` and `F'(V) = colim_{V → V'} F(V')` agree.  The two halves of the
finality criterion are exactly parts (2) and (3) of Stacks 01ZC. -/
theorem final_presentationArrows {P : ObjectProperty (Over S)} {V : Over S} {Λ : Type u}
    [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    {D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory} (c : Cone (D ⋙ (lfpPart P).ι)) (hc : IsLimit c)
    (ci : c.pt ≅ V) (haff : ∀ l, IsAffine (D.obj l).obj.left) :
    (presentationArrows c ci).Final := by
  have hpres : ∀ A : (lfpPart P).FullSubcategory,
      Scheme.IsLimitPreserving S (yoneda.obj A.obj) := by
    intro A
    have : LocallyOfFinitePresentation A.obj.hom := A.property.2
    exact Scheme.isLimitPreserving_yoneda_of_locallyOfFinitePresentation A.obj
  refine Functor.final_of_exists_of_isFiltered _ (fun d => ?_) (fun {d l} s s' => ?_)
  · obtain ⟨l, gl, hgl⟩ := Scheme.exists_comp_eq_of_isLimitPreserving (hpres d.left.unop)
      (D ⋙ (lfpPart P).ι) c hc haff (ci.hom ≫ d.hom.unop)
    refine ⟨l.unop, ⟨CostructuredArrow.homMk (ObjectProperty.homMk gl).op ?_⟩⟩
    apply Quiver.Hom.unop_inj
    have hkey : ci.inv ≫ c.π.app l ≫ gl = d.hom.unop := by
      rw [hgl, Iso.inv_hom_id_assoc]
    simpa using hkey
  · have hs : c.π.app (op l) ≫ (lfpPart P).ι.map s.left.unop
        = c.π.app (op l) ≫ (lfpPart P).ι.map s'.left.unop := by
      have h1 := congrArg Quiver.Hom.unop (CostructuredArrow.w s)
      have h2 := congrArg Quiver.Hom.unop (CostructuredArrow.w s')
      simp only [Functor.op_obj, unop_comp, Quiver.Hom.unop_op, Functor.op_map,
        CostructuredArrow.mk_hom_eq_self, presentationArrows] at h1 h2
      rw [← cancel_epi ci.inv, ← Category.assoc, ← Category.assoc] at *
      rw [h1, h2]
    obtain ⟨j, φ, hj⟩ := exists_map_comp_eq_of_isLimitPreserving (hpres d.left.unop)
      (D ⋙ (lfpPart P).ι) c hc haff _ _ hs
    refine ⟨j.unop, φ.unop, ?_⟩
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    exact (lfpPart P).ι.map_injective (by simpa using hj)

/-! ### The two formulas for the extension on affine objects -/

/-- The value of `affineExtension P F` at `X` is the colimit of `F` over the arrows from `X` into
the objects of the subcategory which are locally of finite presentation over `S`. -/
lemma affineExtension_obj (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) (X : (Over S)ᵒᵖ) :
    (affineExtension P F).obj X =
      colimit (CostructuredArrow.proj (lfpPart P).ι.op X ⋙ lfpRestriction P F) :=
  rfl

/-- **The directed colimit computing the extension on an affine object.** For a presentation
`V = lim V_l` of an affine object of `Sch/S` over an affine open of `S` by objects of the
subcategory which are locally of finite presentation over `S`, the value `F'(V)` of the extension
is the directed colimit `colim_l F(V_l)`: the cocone obtained by restricting the defining colimit
cocone along the presentation is itself a colimit cocone. -/
noncomputable def isColimitPresentationCocone {P : ObjectProperty (Over S)}
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) {V : Over S} {Λ : Type u}
    [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    {D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory} (c : Cone (D ⋙ (lfpPart P).ι)) (hc : IsLimit c)
    (ci : c.pt ≅ V) (haff : ∀ l, IsAffine (D.obj l).obj.left) :
    IsColimit ((colimit.cocone (CostructuredArrow.proj (lfpPart P).ι.op (op V) ⋙
      lfpRestriction P F)).whisker (presentationArrows c ci)) :=
  have := final_presentationArrows c hc ci haff
  (Functor.Final.isColimitWhiskerEquiv (presentationArrows c ci) _).symm (colimit.isColimit _)

/-- **The two formulas of Stacks 0EUW for the extension on an affine object agree.** The colimit
`colim_{V → V'} F(V')` over all arrows into the locally-finitely-presented objects of the
subcategory, which is the formula making the extension a functor, is computed by any presentation
`V = lim V_l` of `V` by such objects. -/
noncomputable def colimitPresentationIso {P : ObjectProperty (Over S)}
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) {V : Over S} {Λ : Type u}
    [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    {D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory} (c : Cone (D ⋙ (lfpPart P).ι)) (hc : IsLimit c)
    (ci : c.pt ≅ V) (haff : ∀ l, IsAffine (D.obj l).obj.left) :
    colimit (presentationArrows c ci ⋙ CostructuredArrow.proj (lfpPart P).ι.op (op V) ⋙
        lfpRestriction P F) ≅ (affineExtension P F).obj (op V) :=
  have := final_presentationArrows c hc ci haff
  Functor.Final.colimitIso (presentationArrows c ci) _

/-! ### The extension agrees with `F` on the objects of the subcategory -/

section Agreement

variable {P : ObjectProperty (Over S)} (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))

/-- For an object `Z` of the subcategory, the cocone with apex `F(Z)` on the diagram whose
colimit is `F'(Z)`: an arrow `Z ⟶ V'` into an object of the subcategory which is locally of
finite presentation over `S` induces a map `F(V') ⟶ F(Z)`, because the subcategory is full. -/
def subcategoryCocone (Z : Over S) (hZ : P Z) :
    Cocone (CostructuredArrow.proj (lfpPart P).ι.op (op Z) ⋙ lfpRestriction P F) where
  pt := F.obj (op ⟨Z, hZ⟩)
  ι :=
    { app d := F.map
        (ObjectProperty.homMk (X := (⟨Z, hZ⟩ : P.FullSubcategory))
          (Y := (lfpIncl P).obj d.left.unop) d.hom.unop).op
      naturality := by
        intro d₁ d₂ φ
        have hkey : (lfpIncl P).op.map φ.left
              ≫ (ObjectProperty.homMk (X := (⟨Z, hZ⟩ : P.FullSubcategory))
                (Y := (lfpIncl P).obj d₂.left.unop) d₂.hom.unop).op
            = (ObjectProperty.homMk (X := (⟨Z, hZ⟩ : P.FullSubcategory))
                (Y := (lfpIncl P).obj d₁.left.unop) d₁.hom.unop).op := by
          apply Quiver.Hom.unop_inj
          refine P.ι.map_injective ?_
          change d₂.hom.unop ≫ φ.left.unop.hom = d₁.hom.unop
          simpa using congrArg Quiver.Hom.unop (CostructuredArrow.w φ)
        change F.map ((lfpIncl P).op.map φ.left) ≫ F.map _ = F.map _ ≫ 𝟙 _
        rw [Category.comp_id, ← Functor.map_comp, hkey] }

/-- A presentation `Z = lim V_l` of an object `Z` of the subcategory, read as a cone inside the
subcategory: the subcategory is full, so the projections `Z ⟶ V_l` are morphisms of it. -/
def presentationConeInSubcategory {Z : Over S} (hZ : P Z) {Λ : Type u} [Preorder Λ]
    {D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory} (c : Cone (D ⋙ (lfpPart P).ι)) (ci : c.pt ≅ Z) :
    Cone (D ⋙ lfpIncl P) where
  pt := ⟨Z, hZ⟩
  π :=
    { app l := ObjectProperty.homMk (ci.inv ≫ c.π.app l)
      naturality := by
        intro l m h
        refine P.ι.map_injective ?_
        change 𝟙 Z ≫ ci.inv ≫ c.π.app m = (ci.inv ≫ c.π.app l) ≫ (D ⋙ (lfpPart P).ι).map h
        rw [Category.id_comp, Category.assoc, c.w h] }

/-- The cone of a presentation, read inside the subcategory, is still a limit cone in `Sch/S`. -/
noncomputable def isLimit_mapCone_presentationConeInSubcategory {Z : Over S} (hZ : P Z)
    {Λ : Type u} [Preorder Λ] {D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory}
    (c : Cone (D ⋙ (lfpPart P).ι)) (ci : c.pt ≅ Z) (hc : IsLimit c) :
    IsLimit (P.ι.mapCone (presentationConeInSubcategory hZ c ci)) :=
  hc.ofIsoLimit (Cone.ext ci (fun j => by
    change c.π.app j = ci.hom ≫ ci.inv ≫ c.π.app j
    rw [Iso.hom_inv_id_assoc]))

/-- **The extension agrees with `F` on the affine objects of the subcategory lying over an affine
open of `S`.** This is the assertion of the source that "if `V` were an object of `𝒞`, then
`F'(V) = F(V)` by assumption (b)": the cocone with apex `F(V)` on the diagram defining `F'(V)` is
a colimit cocone, because the presentation of `V` is cofinal in that diagram and condition (b)
identifies `F(V)` with the directed colimit along the presentation. -/
theorem nonempty_isColimit_subcategoryCocone (hP : HasFinitePresentationAffines P)
    (hbF : PreservesAffineLimitsOnSubcategory P F) (Z : Over S) (hZ : P Z)
    (hZaff : IsAffineOverAffineOpen Z) :
    Nonempty (IsColimit (subcategoryCocone F Z hZ)) := by
  obtain ⟨Λ, _, _, _, D, c, hc, ci, haff⟩ := exists_lfpPresentation hP Z hZaff
  have hfin := final_presentationArrows c hc ci haff
  obtain ⟨hcol⟩ := hbF Λ (D ⋙ lfpIncl P) haff
    (presentationConeInSubcategory hZ c ci)
    (isLimit_mapCone_presentationConeInSubcategory hZ c ci hc)
  refine ⟨Functor.Final.isColimitWhiskerEquiv (presentationArrows c ci) _ ?_⟩
  exact (hcol.whiskerEquivalence (opOpEquivalence Λ).symm).ofIsoColimit
    (Cocone.ext (Iso.refl _) fun _ => rfl)

/-- **The extension agrees with `F`.** For an affine object `Z` of the subcategory lying over an
affine open of `S`, the value of the extension at `Z` is `F(Z)`. -/
theorem nonempty_affineExtensionObjIso (hP : HasFinitePresentationAffines P)
    (hbF : PreservesAffineLimitsOnSubcategory P F) (Z : Over S) (hZ : P Z)
    (hZaff : IsAffineOverAffineOpen Z) :
    Nonempty ((affineExtension P F).obj (op Z) ≅ F.obj (op ⟨Z, hZ⟩)) :=
  (nonempty_isColimit_subcategoryCocone F hP hbF Z hZ hZaff).elim fun h =>
    ⟨IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h⟩

/-- The value of the extension at an affine object `Z` of the subcategory lying over an affine
open of `S` is `F(Z)`. -/
theorem nonempty_extensionObjIso (hP : HasFinitePresentationAffines P)
    (hbF : PreservesAffineLimitsOnSubcategory P F) (Z : Over S) (hZ : P Z)
    (hZaff : IsAffineOverAffineOpen Z) :
    Nonempty ((extension P F).obj (op Z) ≅ F.obj (op ⟨Z, hZ⟩)) :=
  (nonempty_affineExtensionObjIso F hP hbF Z hZ hZaff).elim fun h =>
    ⟨(extensionIsoOnAffine P F).app (op ⟨Z, hZaff⟩) ≪≫ h⟩

end Agreement

end AlgebraicGeometry.ExtendingFunctors

end
