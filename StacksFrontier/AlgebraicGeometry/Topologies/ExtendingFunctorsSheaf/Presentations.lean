module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf.OpenSubobjects

/-!
# Extending functors from a full subcategory of schemes: presentations of affine objects

This is the second part of `StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf`.
It contains the legs `affineExtensionι` of the colimit computing the extension on affine
objects and their naturality, the description of the sections of that colimit through a
presentation of an affine object as a directed inverse limit of objects of the
locally-finitely-presented part (`exists_affineExtensionι_eq`,
`exists_map_eq_of_affineExtensionι_eq`), the restriction of a presentation to the indices
above a given one (`iciIncl`, `isLimitWhiskerIciIncl`, `botToOver`), and the presentations of
the open subobjects of the limit induced by opens of the least stage (`openAt`,
`exists_openPresentation`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.ExtendingFunctors

universe v w u

variable {S : Scheme.{u}}

variable {P : ObjectProperty (Over S)}

/-! ### The colimit computing the extension on affine objects -/

variable (P) (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))

/-- The leg at an arrow `f : Y ⟶ A` into an object of the subcategory which is locally of finite
presentation over `S` of the colimit `colim_{Y → V'} F(V')` computing `affineExtension P F`. -/
noncomputable def affineExtensionι {Y : Over S} (A : (lfpPart P).FullSubcategory) (f : Y ⟶ A.obj) :
    (lfpRestriction P F).obj (op A) ⟶ (affineExtension P F).obj (op Y) :=
  colimit.ι (CostructuredArrow.proj (lfpPart P).ι.op (op Y) ⋙ lfpRestriction P F)
    (CostructuredArrow.mk (Y := op A) f.op)

/-- Precomposing the arrow indexing a leg of the colimit is the action of `affineExtension P F`
on morphisms. -/
lemma affineExtensionι_comp_map {Y Y' : Over S} (g : Y' ⟶ Y)
    (A : (lfpPart P).FullSubcategory) (f : Y ⟶ A.obj) :
    affineExtensionι P F A f ≫ (affineExtension P F).map g.op
      = affineExtensionι P F A (g ≫ f) :=
  colimit.ι_desc _ _

/-- Elementwise form of `affineExtensionι_comp_map`. -/
lemma affineExtensionι_naturality {Y Y' : Over S} (g : Y' ⟶ Y)
    (A : (lfpPart P).FullSubcategory) (f : Y ⟶ A.obj)
    (x : (lfpRestriction P F).obj (op A)) :
    (affineExtension P F).map g.op (affineExtensionι P F A f x)
      = affineExtensionι P F A (g ≫ f) x := by
  have h := ConcreteCategory.congr_hom (affineExtensionι_comp_map P F g A f) x
  simpa using h

/-- Composing the arrow indexing a leg of the colimit with a morphism of the subcategory is the
action of `F` on that morphism. -/
lemma map_comp_affineExtensionι {Y : Over S} {A B : (lfpPart P).FullSubcategory} (h : B ⟶ A)
    (f : Y ⟶ B.obj) :
    (lfpRestriction P F).map h.op ≫ affineExtensionι P F B f
      = affineExtensionι P F A (f ≫ (lfpPart P).ι.map h) := by
  let d₁ : CostructuredArrow (lfpPart P).ι.op (op Y) :=
    CostructuredArrow.mk (Y := op A) (f ≫ (lfpPart P).ι.map h).op
  let d₂ : CostructuredArrow (lfpPart P).ι.op (op Y) := CostructuredArrow.mk (Y := op B) f.op
  exact colimit.w (CostructuredArrow.proj (lfpPart P).ι.op (op Y) ⋙ lfpRestriction P F)
    (CostructuredArrow.homMk (f := d₁) (f' := d₂) h.op rfl)

/-- Elementwise form of `map_comp_affineExtensionι`. -/
lemma affineExtensionι_map {Y : Over S} {A B : (lfpPart P).FullSubcategory} (h : B ⟶ A)
    (f : Y ⟶ B.obj) (x : (lfpRestriction P F).obj (op A)) :
    affineExtensionι P F B f ((lfpRestriction P F).map h.op x)
      = affineExtensionι P F A (f ≫ (lfpPart P).ι.map h) x := by
  have hw := ConcreteCategory.congr_hom (map_comp_affineExtensionι P F h f) x
  simpa using hw

section Presentation

variable {P F}
variable {Y : Over S} {Λ : Type u} [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
  {D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory}

/-- **Every section of the extension over an affine object comes from a stage of a
presentation.** For a presentation `Y = lim V_l` of an affine object of `Sch/S` over an affine
open of `S` by objects of the subcategory which are locally of finite presentation over `S`, the
colimit `F'(Y) = colim_l F(V_l)` is a filtered colimit, so every element of `F'(Y)` is the image
of an element of some `F(V_l)`. -/
theorem exists_affineExtensionι_eq (c : Cone (D ⋙ (lfpPart P).ι)) (hc : IsLimit c)
    (ci : c.pt ≅ Y) (haff : ∀ l, IsAffine (D.obj l).obj.left)
    (x : (affineExtension P F).obj (op Y)) :
    ∃ (l : Λ) (y : (lfpRestriction P F).obj (op (D.obj (op l)))),
      affineExtensionι P F (D.obj (op l)) (ci.inv ≫ c.π.app (op l)) y = x :=
  Types.jointly_surjective_of_isColimit (isColimitPresentationCocone F c hc ci haff) x

/-- **Two sections coming from the same stage of a presentation and agreeing over an affine
object agree at a later stage.** -/
theorem exists_map_eq_of_affineExtensionι_eq (c : Cone (D ⋙ (lfpPart P).ι)) (hc : IsLimit c)
    (ci : c.pt ≅ Y) (haff : ∀ l, IsAffine (D.obj l).obj.left) {l : Λ}
    (y y' : (lfpRestriction P F).obj (op (D.obj (op l))))
    (h : affineExtensionι P F (D.obj (op l)) (ci.inv ≫ c.π.app (op l)) y
      = affineExtensionι P F (D.obj (op l)) (ci.inv ≫ c.π.app (op l)) y') :
    ∃ (m : Λ) (φ : l ⟶ m), (lfpRestriction P F).map (D.map φ.op).op y
      = (lfpRestriction P F).map (D.map φ.op).op y' :=
  (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitPresentationCocone F c hc ci haff) y y').1 h

end Presentation

/-! ### Restricting a presentation to the indices above a given one -/

section Ici

variable {Λ : Type u} [PartialOrder Λ] [IsDirectedOrder Λ]

/-- The set of indices above a given one in a directed poset is directed. -/
lemma isDirectedOrder_Ici (l₀ : Λ) : IsDirectedOrder ↥(Set.Ici l₀) :=
  ⟨fun a b => by
    obtain ⟨m, ham, hbm⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨m, le_trans a.2 ham⟩, ham, hbm⟩⟩

/-- The inclusion of the indices above a given one into a directed poset. -/
def iciIncl (l₀ : Λ) : ↥(Set.Ici l₀) ⥤ Λ :=
  Monotone.functor (f := ((↑) : ↥(Set.Ici l₀) → Λ)) fun _ _ h => h

/-- The inclusion of the indices above a given one into a directed poset is final. -/
lemma final_iciIncl (l₀ : Λ) : (iciIncl l₀).Final :=
  have := isDirectedOrder_Ici l₀
  (Monotone.final_functor_iff (f := ((↑) : ↥(Set.Ici l₀) → Λ)) fun _ _ h => h).2 fun j => by
    obtain ⟨m, hjm, h₀m⟩ := exists_ge_ge j l₀
    exact ⟨⟨m, h₀m⟩, hjm⟩

/-- Restricting an inverse system to the indices above a given one does not change the limit. -/
noncomputable def isLimitWhiskerIciIncl (l₀ : Λ) {C : Type*} [Category C] {D : Λᵒᵖ ⥤ C}
    (c : Cone D) (hc : IsLimit c) : IsLimit (Cone.whisker (iciIncl l₀).op c) :=
  haveI := final_iciIncl l₀
  haveI := Functor.initial_op_of_final (iciIncl l₀)
  (Functor.Initial.isLimitWhiskerEquiv (iciIncl l₀).op c).symm hc

end Ici

/-- The opposite of a poset with a least element, read as the arrows into the least
element in the opposite poset. -/
def botToOver (Λ : Type u) [PartialOrder Λ] [OrderBot Λ] : Λᵒᵖ ⥤ Over (op (⊥ : Λ)) where
  obj l := Over.mk (homOfLE (bot_le : (⊥ : Λ) ≤ l.unop)).op
  map {l m} φ := Over.homMk φ (Subsingleton.elim _ _)
  map_id l := by apply Over.OverMorphism.ext; exact Subsingleton.elim _ _
  map_comp f g := by apply Over.OverMorphism.ext; exact Subsingleton.elim _ _

/-- The arrows into the least element of a directed poset with a least element are
cofinal in its opposite. -/
lemma initial_botToOver (Λ : Type u) [PartialOrder Λ] [OrderBot Λ] [IsDirectedOrder Λ] :
    (botToOver Λ).Initial := by
  refine Functor.initial_of_exists_of_isCofiltered _ (fun d => ?_) (fun s s' => ?_)
  · exact ⟨d.left, ⟨Over.homMk (𝟙 _) (Subsingleton.elim _ _)⟩⟩
  · exact ⟨_, 𝟙 _, by apply Over.OverMorphism.ext; exact Subsingleton.elim _ _⟩

variable {P : ObjectProperty (Over S)}

/-- The morphism of the locally-finitely-presented part of the subcategory attached to an
identification of an open subobject of one of its objects with another of its objects. -/
noncomputable def lfpOpenSubHom {A B : (lfpPart P).FullSubcategory} {V : A.obj.left.Opens}
    (e : overOpen A.obj V ≅ B.obj) : B ⟶ A :=
  ObjectProperty.homMk (e.inv ≫ overOpenι A.obj V)

/-- The image of `lfpOpenSubHom e` under `lfpIncl P` is `openSubHom A.property.1 e`. -/
lemma lfpIncl_map_lfpOpenSubHom {A B : (lfpPart P).FullSubcategory} {V : A.obj.left.Opens}
    (e : overOpen A.obj V ≅ B.obj) :
    (lfpIncl P).map (lfpOpenSubHom e) = openSubHom A.property.1 e := rfl

/-- In `Sch/S`, `lfpOpenSubHom e` is `e.inv` followed by the inclusion of `V`. -/
@[simp]
lemma ι_map_lfpOpenSubHom {A B : (lfpPart P).FullSubcategory} {V : A.obj.left.Opens}
    (e : overOpen A.obj V ≅ B.obj) :
    (lfpPart P).ι.map (lfpOpenSubHom e) = e.inv ≫ overOpenι A.obj V := rfl

section OpenPresentation

variable {Λ : Type u} [PartialOrder Λ] [OrderBot Λ]
  {D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory}

/-- The inverse image at the stage `l` of an open of the least stage of a presentation. -/
def openAt (W : (D.obj (op (⊥ : Λ))).obj.left.Opens) (l : Λ) :
    (D.obj (op l)).obj.left.Opens :=
  ((D ⋙ (lfpPart P).ι).map (homOfLE (bot_le : (⊥ : Λ) ≤ l)).op).left ⁻¹ᵁ W

/-- The opens `openAt W l` are compatible with the transition morphisms of the presentation. -/
lemma openAt_preimage (W : (D.obj (op (⊥ : Λ))).obj.left.Opens) {l m : Λᵒᵖ} (φ : l ⟶ m) :
    ((D ⋙ (lfpPart P).ι).map φ).left ⁻¹ᵁ (openAt W m.unop) = openAt W l.unop := by
  have h : φ ≫ (homOfLE (bot_le : (⊥ : Λ) ≤ m.unop)).op
      = (homOfLE (bot_le : (⊥ : Λ) ≤ l.unop)).op := Subsingleton.elim _ _
  rw [openAt, openAt, ← Scheme.Hom.comp_preimage, ← Over.comp_left, ← Functor.map_comp, h]

/-- The inverse image in the limit of a presentation of the opens `openAt W l` is independent
of the stage. -/
lemma preimage_openAt (c : Cone (D ⋙ (lfpPart P).ι))
    (W : (D.obj (op (⊥ : Λ))).obj.left.Opens) (l : Λᵒᵖ) :
    (c.π.app l).left ⁻¹ᵁ (openAt W l.unop) = (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W := by
  rw [openAt, ← Scheme.Hom.comp_preimage, ← Over.comp_left, c.w]

/-- The structure morphisms over `S` of the open subobjects `openAt W l` of the stages of a
presentation. -/
noncomputable def openAtToBase (W : (D.obj (op (⊥ : Λ))).obj.left.Opens) :
    (botToOver Λ ⋙ opensDiagram ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S) (op (⊥ : Λ)) W) ⟶
      (Functor.const Λᵒᵖ).obj S where
  app l := (openAt W l.unop).ι ≫ (D.obj l).obj.hom
  naturality := by
    intro l m φ
    have h1 := Scheme.Hom.resLE_comp_ι (((D ⋙ (lfpPart P).ι) ⋙ Over.forget S).map φ)
      (U := openAt W m.unop) (V := openAt W l.unop) (le_of_eq (openAt_preimage W φ).symm)
    have h2 : ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S).map φ ≫ (D.obj m).obj.hom
        = (D.obj l).obj.hom := Over.w ((D ⋙ (lfpPart P).ι).map φ)
    have key : (opensDiagram ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S) (op (⊥ : Λ)) W).map
          ((botToOver Λ).map φ)
        = Scheme.Hom.resLE (((D ⋙ (lfpPart P).ι) ⋙ Over.forget S).map φ)
          (openAt W m.unop) (openAt W l.unop) (le_of_eq (openAt_preimage W φ).symm) := rfl
    simp only [Functor.comp_map, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [key]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ (D.obj m).obj.hom) h1).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (fun k => (openAt W l.unop).ι ≫ k) h2

/-- The component of `openAtToBase W` at `l` is the inclusion of `openAt W l` followed by the
structure morphism of the stage `l`. -/
@[simp]
lemma openAtToBase_app (W : (D.obj (op (⊥ : Λ))).obj.left.Opens) (l : Λᵒᵖ) :
    (openAtToBase W).app l = (openAt W l.unop).ι ≫ (D.obj l).obj.hom :=
  rfl

variable [IsDirectedOrder Λ]

/-- **The open subobjects of a presentation.** Let `X = lim_l V_l` be a presentation of an object
of `Sch/S` by affine objects of the subcategory which are locally of finite presentation over
`S`, indexed by the opposite of a directed poset with a least element, and let `W` be an
affine open of the least stage. The open subobject of `X` over the inverse image of `W` is then
the limit of the open subobjects `openAt W l` of the stages, and condition (1) of Stacks 0EUW
identifies each of those with an object of the subcategory, again affine and locally of finite
presentation over `S`. The inclusions of the open subobjects assemble into a morphism of inverse
systems. -/
theorem exists_openPresentation (hP1 : HasAffineOpens P)
    (c : Cone (D ⋙ (lfpPart P).ι)) (hc : IsLimit c)
    (haff : ∀ l, IsAffine (D.obj l).obj.left)
    (W : (D.obj (op (⊥ : Λ))).obj.left.Opens) (hW : IsAffineOpen W) :
    ∃ (D' : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory) (r : D' ⟶ D)
      (π' : (Functor.const Λᵒᵖ).obj (overOpen c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W)) ⟶
        D' ⋙ (lfpPart P).ι)
      (_ : IsLimit (Cone.mk _ π')) (_ : ∀ l, IsAffine (D'.obj l).obj.left)
      (e : ∀ l : Λᵒᵖ, overOpen (D.obj l).obj (openAt W l.unop) ≅ (D'.obj l).obj),
      (∀ l, (lfpPart P).ι.map (r.app l)
        = (e l).inv ≫ overOpenι (D.obj l).obj (openAt W l.unop)) ∧
      ∀ l, π'.app l ≫ (lfpPart P).ι.map (r.app l)
        = overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W) ≫ c.π.app l := by
  classical
  have hDaff : ∀ l, IsAffine (((D ⋙ (lfpPart P).ι) ⋙ Over.forget S).obj l) := haff
  have hAffHom : ∀ {i j : Λᵒᵖ} (f : i ⟶ j),
      IsAffineHom (((D ⋙ (lfpPart P).ι) ⋙ Over.forget S).map f) := by
    intro i j f
    have := hDaff i
    have := hDaff j
    exact isAffineHom_of_isAffine _
  have hcsch : IsLimit ((Over.forget S).mapCone c) := isLimitOfPreserves (Over.forget S) hc
  have := initial_botToOver Λ
  have hlim := (Functor.Initial.isLimitWhiskerEquiv (botToOver Λ)
      (opensCone ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S) ((Over.forget S).mapCone c)
        (op (⊥ : Λ)) W)).symm
    (isLimitOpensCone ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S) ((Over.forget S).mapCone c)
      hcsch (op (⊥ : Λ)) W)
  have hp : ∀ l : Λᵒᵖ, (Cone.whisker (botToOver Λ)
      (opensCone ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S) ((Over.forget S).mapCone c)
        (op (⊥ : Λ)) W)).π.app l ≫ (openAtToBase W).app l
      = ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W).ι ≫ c.pt.hom := by
    intro l
    have key : (Cone.whisker (botToOver Λ)
          (opensCone ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S) ((Over.forget S).mapCone c)
            (op (⊥ : Λ)) W)).π.app l
        = Scheme.Hom.resLE (c.π.app l).left (openAt W l.unop)
          ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W) (le_of_eq (preimage_openAt c W l).symm) := rfl
    rw [key, openAtToBase_app]
    exact (Scheme.Hom.resLE_comp_ι_assoc ..).trans
      (congrArg (((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W).ι ≫ ·) (Over.w (c.π.app l)))
  have hclift := Over.isLimitLiftCone _ (openAtToBase W) _ _ hp hlim
  have hOpen : ∀ l : Λᵒᵖ, IsAffineOpen (openAt W l.unop) := by
    intro l
    have := hAffHom ((homOfLE (bot_le : (⊥ : Λ) ≤ l.unop)).op)
    exact hW.preimage _
  have hmem : ∀ l : Λᵒᵖ, ∃ Y : Over S, lfpPart P Y ∧
      Nonempty (overOpen (D.obj l).obj (openAt W l.unop) ≅ Y) := by
    intro l
    have haffl : IsAffine (D.obj l).obj.left := haff l
    obtain ⟨Y, hPY, ⟨i⟩⟩ := hP1 (D.obj l).obj (D.obj l).property.1 ⟨openAt W l.unop, hOpen l⟩
    refine ⟨Y, ⟨hPY, ?_⟩, ⟨i⟩⟩
    have hlfp : LocallyOfFinitePresentation (D.obj l).obj.hom := (D.obj l).property.2
    have hw : i.inv.left ≫ (overOpen (D.obj l).obj (openAt W l.unop)).hom = Y.hom := Over.w i.inv
    have hiso : IsIso i.inv.left := inferInstanceAs (IsIso ((Over.forget S).map i.inv))
    rw [← hw]
    exact inferInstanceAs (LocallyOfFinitePresentation
      (i.inv.left ≫ (openAt W l.unop).ι ≫ (D.obj l).obj.hom))
  choose Y hY e using hmem
  have hGι : ∀ {l m : Λᵒᵖ} (φ : l ⟶ m),
      (Over.lift (botToOver Λ ⋙ opensDiagram ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S)
          (op (⊥ : Λ)) W) (openAtToBase W)).map φ
          ≫ overOpenι (D.obj m).obj (openAt W m.unop)
        = overOpenι (D.obj l).obj (openAt W l.unop) ≫ (D ⋙ (lfpPart P).ι).map φ := by
    intro l m φ
    refine Over.OverMorphism.ext ?_
    simp only [Over.comp_left, overOpenι_left, Over.lift_map]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hnat : ∀ {l m : Λᵒᵖ} (φ : l ⟶ m),
      ((Over.lift (botToOver Λ ⋙ opensDiagram ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S)
            (op (⊥ : Λ)) W) (openAtToBase W)).copyObj Y (fun l => (e l).some)).map φ
          ≫ ((e m).some.inv ≫ overOpenι (D.obj m).obj (openAt W m.unop))
        = ((e l).some.inv ≫ overOpenι (D.obj l).obj (openAt W l.unop))
          ≫ (D ⋙ (lfpPart P).ι).map φ := by
    intro l m φ
    change ((e l).some.inv ≫ _ ≫ (e m).some.hom) ≫ _ = _
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine congrArg (fun k => (e l).some.inv ≫ k) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k => _ ≫ k) (Iso.hom_inv_id_assoc (e m).some _)) ?_
    exact hGι φ
  refine ⟨(lfpPart P).lift ((Over.lift _ (openAtToBase W)).copyObj Y (fun l => (e l).some)) hY,
    { app l := lfpOpenSubHom (e l).some
      naturality := fun l m φ => (lfpPart P).ι.map_injective (by
        refine Eq.trans (Functor.map_comp _ _ _) ?_
        refine Eq.trans ?_ (Functor.map_comp _ _ _).symm
        exact hnat φ) },
    ((Cone.postcompose (Functor.isoCopyObj (Over.lift _ (openAtToBase W)) Y
      (fun l => (e l).some)).hom).obj (Over.liftCone _ (openAtToBase W) _ _ hp)).π,
    (IsLimit.postcomposeHomEquiv _ _).symm hclift, ?_, (fun l => (e l).some),
    (fun l => rfl), ?_⟩
  · intro l
    have h0 : IsAffine (overOpen (D.obj l).obj (openAt W l.unop)).left := hOpen l
    have h2 : IsAffine (Y l).left := by
      have eiso : (Y l).left ≅ (overOpen (D.obj l).obj (openAt W l.unop)).left :=
        ((Over.forget S).mapIso (e l).some).symm
      exact IsAffine.of_isIso eiso.hom
    exact h2
  · intro l
    have hkey : (Over.liftCone
          (botToOver Λ ⋙ opensDiagram ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S) (op (⊥ : Λ)) W)
          (openAtToBase W)
          (Cone.whisker (botToOver Λ)
            (opensCone ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S) ((Over.forget S).mapCone c)
              (op (⊥ : Λ)) W))
          (((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W).ι ≫ c.pt.hom) hp).π.app l
          ≫ overOpenι (D.obj l).obj (openAt W l.unop)
        = overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W) ≫ c.π.app l := by
      refine Over.OverMorphism.ext ?_
      simp only [Over.comp_left, overOpenι_left]
      exact Scheme.Hom.resLE_comp_ι _ _
    refine Eq.trans ?_ hkey
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact congrArg (fun k => _ ≫ k) (Iso.hom_inv_id_assoc (e l).some _)

end OpenPresentation

end AlgebraicGeometry.ExtendingFunctors

end
