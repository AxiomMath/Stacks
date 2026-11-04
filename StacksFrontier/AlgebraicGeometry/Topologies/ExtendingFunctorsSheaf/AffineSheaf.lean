module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf.Presentations

/-!
# Extending functors from a full subcategory of schemes: the affine sheaf condition

This is the third part of `StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf`.
It contains the sheaf condition for one covering by open subobjects (`IsSheafForOpens`), the
presentations adapted to a finite affine open covering (`exists_lfpPresentation_covering`,
where Stacks 01Z4 enters), and the sheaf condition for the colimit formula on a finite covering
of an affine object by affine opens (`isSheafForOpens_affineExtension`).

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.ExtendingFunctors

universe v w u

variable {S : Scheme.{u}}

variable {P : ObjectProperty (Over S)}

variable (P) (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))

variable {P : ObjectProperty (Over S)}

/-! ### The affine sheaf condition for the colimit formula -/

/-- A finite family in a nonempty directed poset has an upper bound. -/
lemma exists_upper_bound {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    {ι : Type*} [Finite ι] (f : ι → Λ) : ∃ m, ∀ i, f i ≤ m := by
  classical
  cases nonempty_fintype ι
  obtain ⟨m, hm⟩ := Finset.exists_le (Finset.univ.image f)
  exact ⟨m, fun i => hm _ (Finset.mem_image_of_mem f (Finset.mem_univ i))⟩

/-- The morphism of the locally-finitely-presented part of the subcategory attached to an
inclusion of open subobjects of one of its objects and identifications of the two open
subobjects with objects of the subcategory. -/
noncomputable def lfpOpenLEHom {A B B' : (lfpPart P).FullSubcategory} {V V' : A.obj.left.Opens}
    (h : V' ≤ V) (e : overOpen A.obj V ≅ B.obj) (e' : overOpen A.obj V' ≅ B'.obj) : B' ⟶ B :=
  ObjectProperty.homMk (e'.inv ≫ overOpenLE A.obj h ≫ e.hom)

/-- The image of `lfpOpenLEHom h e e'` under `lfpIncl P` is `openLEHom h e e'`. -/
lemma lfpIncl_map_lfpOpenLEHom {A B B' : (lfpPart P).FullSubcategory} {V V' : A.obj.left.Opens}
    (h : V' ≤ V) (e : overOpen A.obj V ≅ B.obj) (e' : overOpen A.obj V' ≅ B'.obj) :
    (lfpIncl P).map (lfpOpenLEHom h e e')
      = openLEHom (P := P) (A := (lfpIncl P).obj B) (A' := (lfpIncl P).obj B') h e e' := rfl

/-- In `Sch/S`, `lfpOpenLEHom h e e'` is `e'.inv`, followed by the inclusion `V' ≤ V`, followed
by `e.hom`. -/
@[simp]
lemma ι_map_lfpOpenLEHom {A B B' : (lfpPart P).FullSubcategory} {V V' : A.obj.left.Opens}
    (h : V' ≤ V) (e : overOpen A.obj V ≅ B.obj) (e' : overOpen A.obj V' ≅ B'.obj) :
    (lfpPart P).ι.map (lfpOpenLEHom h e e') = e'.inv ≫ overOpenLE A.obj h ≫ e.hom := rfl

/-- The inclusion of an open subobject of an object of `Sch/S`, read through an identification of
that open subobject with another object, is a monomorphism. -/
lemma eq_of_comp_openSub_eq {Y B C : Over S} {V : C.left.Opens} (e : overOpen C V ≅ B)
    {f g : Y ⟶ B} (hfg : f ≫ e.inv ≫ overOpenι C V = g ≫ e.inv ≫ overOpenι C V) : f = g := by
  refine Over.OverMorphism.ext ?_
  have h1 : f.left ≫ e.inv.left ≫ V.ι = g.left ≫ e.inv.left ≫ V.ι := by
    have := congrArg Over.Hom.left hfg
    simpa only [Over.comp_left, overOpenι_left] using this
  rw [← Category.assoc, ← Category.assoc] at h1
  exact (cancel_mono e.inv.left).mp ((cancel_mono V.ι).mp h1)

/-- Two morphisms of the subcategory into an object identified with an open subobject agree as
soon as they agree after composition with the inclusion of that open subobject. -/
lemma lfp_eq_of_comp_eq {A B C : (lfpPart P).FullSubcategory} (h : B ⟶ C)
    {V : C.obj.left.Opens} {e : overOpen C.obj V ≅ B.obj}
    (he : (lfpPart P).ι.map h = e.inv ≫ overOpenι C.obj V)
    {f g : A ⟶ B} (hfg : f ≫ h = g ≫ h) : f = g := by
  refine (lfpPart P).ι.map_injective (eq_of_comp_openSub_eq e ?_)
  rw [← he, ← Functor.map_comp, ← Functor.map_comp, hfg]

/-- The sheaf condition for a single covering of an object of `Sch/S` by open subobjects. -/
def IsSheafForOpens (F : (Over S)ᵒᵖ ⥤ Type w) (X : Over S) {ι : Type u}
    (V : ι → X.left.Opens) : Prop :=
  ∀ (s : ∀ i, F.obj (op (overOpen X (V i)))),
    (∀ i j, F.map (overOpenLE X (inf_le_left : V i ⊓ V j ≤ V i)).op (s i)
      = F.map (overOpenLE X (inf_le_right : V i ⊓ V j ≤ V j)).op (s j)) →
      ∃! t : F.obj (op X), ∀ i, F.map (overOpenι X (V i)).op t = s i

/-- A presheaf on `Sch/S` is a Zariski sheaf if and only if it satisfies the sheaf condition for
every covering of an object of `Sch/S` by open subobjects. -/
lemma isZariskiSheaf_iff_isSheafForOpens (F : (Over S)ᵒᵖ ⥤ Type w) :
    IsZariskiSheaf F ↔ ∀ (X : Over S) (ι : Type u) (V : ι → X.left.Opens),
      (⨆ i, V i = ⊤) → IsSheafForOpens F X V :=
  Iff.rfl

section ColimitCone

variable {F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))} {Λ : Type u} [PartialOrder Λ]
  {D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory} {Y : Over S}

/-- Pushing a section forward along a transition morphism of a presentation does not change the
element of the colimit computing the extension that it represents. -/
lemma affineExtensionι_cone_map (π : (Functor.const Λᵒᵖ).obj Y ⟶ D ⋙ (lfpPart P).ι)
    {l m : Λ} (φ : l ⟶ m) (x : (lfpRestriction P F).obj (op (D.obj (op l)))) :
    affineExtensionι P F (D.obj (op m)) (π.app (op m))
        ((lfpRestriction P F).map (D.map φ.op).op x)
      = affineExtensionι P F (D.obj (op l)) (π.app (op l)) x := by
  have hn : π.app (op m) ≫ (lfpPart P).ι.map (D.map φ.op) = π.app (op l) := by
    simpa using (π.naturality φ.op).symm
  rw [affineExtensionι_map, hn]

/-- Transition maps of the values of `F` along a presentation compose. -/
lemma lfpRestriction_map_trans {l m n : Λ} (h₁ : l ≤ m) (h₂ : m ≤ n)
    (x : (lfpRestriction P F).obj (op (D.obj (op l)))) :
    (lfpRestriction P F).map (D.map (homOfLE h₂).op).op
        ((lfpRestriction P F).map (D.map (homOfLE h₁).op).op x)
      = (lfpRestriction P F).map (D.map (homOfLE (h₁.trans h₂)).op).op x := by
  have h : ((D.map (homOfLE h₁).op).op ≫ (D.map (homOfLE h₂).op).op :
        op (D.obj (op l)) ⟶ op (D.obj (op n)))
      = (D.map (homOfLE (h₁.trans h₂)).op).op := by
    apply Quiver.Hom.unop_inj
    rw [unop_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op, Quiver.Hom.unop_op,
      ← Functor.map_comp]
    exact congrArg D.map (Subsingleton.elim _ _)
  rw [← h, Functor.map_comp]
  rfl

variable [Nonempty Λ] [IsDirectedOrder Λ]

/-- **Every section of the extension over the limit of a presentation comes from a stage.** -/
theorem exists_affineExtensionι_eq_of_isLimit
    (π : (Functor.const Λᵒᵖ).obj Y ⟶ D ⋙ (lfpPart P).ι) (hπ : IsLimit (Cone.mk Y π))
    (haff : ∀ l, IsAffine (D.obj l).obj.left) (x : (affineExtension P F).obj (op Y)) :
    ∃ (l : Λ) (y : (lfpRestriction P F).obj (op (D.obj (op l)))),
      affineExtensionι P F (D.obj (op l)) (π.app (op l)) y = x := by
  obtain ⟨l, y, hy⟩ := exists_affineExtensionι_eq (Cone.mk Y π) hπ (Iso.refl Y) haff x
  refine ⟨l, y, ?_⟩
  have hid : (Iso.refl Y).inv ≫ (Cone.mk Y π).π.app (op l) = π.app (op l) := Category.id_comp _
  rw [← hid]
  exact hy

/-- **Two sections from the same stage of a presentation which agree over the limit agree at a
later stage.** -/
theorem exists_map_eq_of_affineExtensionι_eq_of_isLimit
    (π : (Functor.const Λᵒᵖ).obj Y ⟶ D ⋙ (lfpPart P).ι) (hπ : IsLimit (Cone.mk Y π))
    (haff : ∀ l, IsAffine (D.obj l).obj.left) {l : Λ}
    (y y' : (lfpRestriction P F).obj (op (D.obj (op l))))
    (h : affineExtensionι P F (D.obj (op l)) (π.app (op l)) y
      = affineExtensionι P F (D.obj (op l)) (π.app (op l)) y') :
    ∃ (m : Λ) (φ : l ⟶ m), (lfpRestriction P F).map (D.map φ.op).op y
      = (lfpRestriction P F).map (D.map φ.op).op y' := by
  have hid : (Iso.refl Y).inv ≫ (Cone.mk Y π).π.app (op l) = π.app (op l) := Category.id_comp _
  exact exists_map_eq_of_affineExtensionι_eq (Cone.mk Y π) hπ (Iso.refl Y) haff y y'
    (by rw [hid]; exact h)

end ColimitCone


/-! ### Presentations adapted to a finite affine open covering -/

/-- **A presentation adapted to a finite covering by affine opens.** An affine object of `Sch/S`
lying over an affine open of `S`, together with a finite covering of it by affine opens, is a
directed inverse limit of affine objects of the subcategory which are locally of finite
presentation over `S`, indexed by a poset with a least element, in such a way that the
members of the covering are the inverse images of affine opens of the least stage.

This is the application of Stacks 01Z4 in the proof of Stacks 0EUW: a finite affine open covering
of a directed inverse limit of affine schemes already comes from a finite stage. -/
theorem exists_lfpPresentation_covering (hP2 : HasFinitePresentationAffines P)
    (X : Over S) (hX : IsAffineOverAffineOpen X) {ι : Type u} [Finite ι]
    (V : ι → X.left.Opens) (hV : ⨆ i, V i = ⊤) (hVaff : ∀ i, IsAffineOpen (V i)) :
    ∃ (Λ : Type u) (_ : PartialOrder Λ) (_ : OrderBot Λ) (_ : IsDirectedOrder Λ)
      (D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory)
      (π : (Functor.const Λᵒᵖ).obj X ⟶ D ⋙ (lfpPart P).ι) (_ : IsLimit (Cone.mk X π))
      (_ : ∀ l, IsAffine (D.obj l).obj.left)
      (W : ι → (D.obj (op (⊥ : Λ))).obj.left.Opens),
      (⨆ i, W i = ⊤) ∧ (∀ i, IsAffineOpen (W i)) ∧
        ∀ i, V i = (π.app (op (⊥ : Λ))).left ⁻¹ᵁ W i := by
  classical
  obtain ⟨Λ₀, _, _, _, D₀, c₀, hc₀, ci₀, haff₀⟩ := exists_lfpPresentation hP2 X hX
  have hcX : IsLimit (c₀.extend ci₀.inv) :=
    hc₀.ofIsoLimit (Cone.ext ci₀ (fun j => (Iso.hom_inv_id_assoc ci₀ (c₀.π.app j)).symm))
  have hDaff₀ : ∀ l, IsAffine (((D₀ ⋙ (lfpPart P).ι) ⋙ Over.forget S).obj l) := haff₀
  have hAffHom₀ : ∀ {i j : Λ₀ᵒᵖ} (f : i ⟶ j),
      IsAffineHom (((D₀ ⋙ (lfpPart P).ι) ⋙ Over.forget S).map f) := by
    intro i j f
    have := hDaff₀ i
    have := hDaff₀ j
    exact isAffineHom_of_isAffine _
  have hCS₀ : ∀ i : Λ₀ᵒᵖ, CompactSpace (((D₀ ⋙ (lfpPart P).ι) ⋙ Over.forget S).obj i) := by
    intro i
    have := hDaff₀ i
    infer_instance
  have hQS₀ : ∀ i : Λ₀ᵒᵖ,
      QuasiSeparatedSpace (((D₀ ⋙ (lfpPart P).ι) ⋙ Over.forget S).obj i) := by
    intro i
    have := hDaff₀ i
    infer_instance
  have hcsch : IsLimit ((Over.forget S).mapCone (c₀.extend ci₀.inv)) :=
    isLimitOfPreserves (Over.forget S) hcX
  obtain ⟨l₀, W₀, hW₀cov, hW₀⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite
    ((D₀ ⋙ (lfpPart P).ι) ⋙ Over.forget S) ((Over.forget S).mapCone (c₀.extend ci₀.inv))
    hcsch V hV hVaff
  have hdir : IsDirectedOrder ↥(Set.Ici l₀.unop) := isDirectedOrder_Ici l₀.unop
  refine ⟨↥(Set.Ici l₀.unop), inferInstance, Set.Ici.orderBot, hdir,
    (iciIncl l₀.unop).op ⋙ D₀,
    (Cone.whisker (iciIncl l₀.unop).op (c₀.extend ci₀.inv)).π,
    isLimitWhiskerIciIncl l₀.unop (c₀.extend ci₀.inv) hcX, fun l => haff₀ _, W₀,
    hW₀cov, fun i => (hW₀ i).1, fun i => (hW₀ i).2⟩



/-- Composing two transition maps of the values of `F`. -/
private theorem lfpRestriction_map_comp_apply_aux {F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))}
    {A B C : (lfpPart P).FullSubcategory} (a : A ⟶ B) (b : B ⟶ C)
    (z : (lfpRestriction P F).obj (op C)) :
    (lfpRestriction P F).map (a ≫ b).op z
      = (lfpRestriction P F).map a.op ((lfpRestriction P F).map b.op z) := by
  rw [op_comp, Functor.map_comp]
  rfl

/-- A morphism of presentations commutes with the transition maps of the values of `F`. -/
lemma lfpRestriction_map_app_comm {F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))}
    {Λ : Type u} [PartialOrder Λ] {A B : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory} (r : A ⟶ B)
    {l m : Λ} (φ : l ⟶ m) (z : (lfpRestriction P F).obj (op (B.obj (op l)))) :
    (lfpRestriction P F).map (A.map φ.op).op ((lfpRestriction P F).map (r.app (op l)).op z)
      = (lfpRestriction P F).map (r.app (op m)).op
        ((lfpRestriction P F).map (B.map φ.op).op z) := by
  rw [← lfpRestriction_map_comp_apply_aux, ← lfpRestriction_map_comp_apply_aux, r.naturality φ.op]


/-- Composing two transition maps of the values of `F`. -/
lemma lfpRestriction_map_comp_apply {F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))}
    {A B C : (lfpPart P).FullSubcategory} (a : A ⟶ B) (b : B ⟶ C)
    (z : (lfpRestriction P F).obj (op C)) :
    (lfpRestriction P F).map (a ≫ b).op z
      = (lfpRestriction P F).map a.op ((lfpRestriction P F).map b.op z) :=
  lfpRestriction_map_comp_apply_aux a b z

section ColimitCone2

variable {F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))} {Λ : Type u} [PartialOrder Λ]
  [Nonempty Λ] [IsDirectedOrder Λ] {D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory} {Y : Over S}

/-- **Two sections from the same stage of a presentation which agree over the limit agree at a
later stage**, with the later stage given by an inequality of indices. -/
theorem exists_le_map_eq_of_affineExtensionι_eq
    (π : (Functor.const Λᵒᵖ).obj Y ⟶ D ⋙ (lfpPart P).ι) (hπ : IsLimit (Cone.mk Y π))
    (haff : ∀ l, IsAffine (D.obj l).obj.left) {l : Λ}
    (y y' : (lfpRestriction P F).obj (op (D.obj (op l))))
    (h : affineExtensionι P F (D.obj (op l)) (π.app (op l)) y
      = affineExtensionι P F (D.obj (op l)) (π.app (op l)) y') :
    ∃ (m : Λ) (hm : l ≤ m), (lfpRestriction P F).map (D.map (homOfLE hm).op).op y
      = (lfpRestriction P F).map (D.map (homOfLE hm).op).op y' := by
  obtain ⟨m, φ, hφ⟩ := exists_map_eq_of_affineExtensionι_eq_of_isLimit π hπ haff y y' h
  refine ⟨m, leOfHom φ, ?_⟩
  have he : homOfLE (leOfHom φ) = φ := Subsingleton.elim _ _
  rw [he]
  exact hφ

end ColimitCone2

/-! ### The sheaf condition for the colimit formula on affine objects -/

/-- **The sheaf condition for the colimit formula on affine objects.** This is the second
paragraph of the proof of Stacks 0EUW. Write the affine object as a directed inverse limit of
objects of the subcategory which are locally of finite presentation over `S`; by Stacks 01Z4 a
finite covering by affine opens comes from a finite stage, where condition (a) applies, and the
sheaf condition passes to the colimit because a directed colimit of sets commutes with finite
limits. -/
theorem isSheafForOpens_affineExtension (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P) {F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))}
    (haF : IsZariskiSheafOnSubcategory P F) (X : Over S) (hX : IsAffineOverAffineOpen X)
    {ι : Type u} [Finite ι] (V : ι → X.left.Opens) (hV : ⨆ i, V i = ⊤)
    (hVaff : ∀ i, IsAffineOpen (V i)) :
    IsSheafForOpens (affineExtension P F) X V := by
  classical
  obtain ⟨Λ, _, _, _, D, π, hπ, haff, W, hWcov, hWaff, hVW⟩ :=
    exists_lfpPresentation_covering hP2 X hX V hV hVaff
  have hVeq : V = fun i => (π.app (op (⊥ : Λ))).left ⁻¹ᵁ W i := funext hVW
  subst hVeq
  have hbot : ∀ l : Λᵒᵖ, IsAffine (D.obj l).obj.left := haff
  choose Dj rj πj hπj haffj ej hrj1 hrj2 using fun i =>
    exists_openPresentation hP1 (Cone.mk X π) hπ haff (W i) (hWaff i)
  choose Djk rjk πjk hπjk haffjk ejk hrjk1 hrjk2 using fun (i k : ι) =>
    exists_openPresentation hP1 (Cone.mk X π) hπ haff (W i ⊓ W k)
      (by have := hbot (op (⊥ : Λ)); exact (hWaff i).inf (hWaff k))
  -- the opens of the stages, and the inclusions among them
  have hinf : ∀ (i k : ι) (l : Λᵒᵖ),
      openAt (W i ⊓ W k) l.unop = openAt (W i) l.unop ⊓ openAt (W k) l.unop :=
    fun _ _ _ => rfl
  have hle : ∀ (i k : ι) (l : Λᵒᵖ), openAt (W i ⊓ W k) l.unop ≤ openAt (W i) l.unop :=
    fun i k l => (hinf i k l).le.trans inf_le_left
  have hle' : ∀ (i k : ι) (l : Λᵒᵖ), openAt (W i ⊓ W k) l.unop ≤ openAt (W k) l.unop :=
    fun i k l => (hinf i k l).le.trans inf_le_right
  -- the comparison morphisms of the presentations
  have hC6 : ∀ (i k : ι) {j : ι} (l : Λᵒᵖ) (h : openAt (W i ⊓ W k) l.unop ≤ openAt (W j) l.unop),
      lfpOpenLEHom h (ej j l) (ejk i k l) ≫ (rj j).app l = (rjk i k).app l := by
    intro i k j l h
    refine (lfpPart P).ι.map_injective ?_
    rw [Functor.map_comp, ι_map_lfpOpenLEHom, hrj1 j l, hrjk1 i k l]
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine congrArg (fun z => (ejk i k l).inv ≫ z) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z => _ ≫ z) (Iso.hom_inv_id_assoc (ej j l) _)) ?_
    exact overOpenLE_comp_overOpenι _ _
  have hrjP : ∀ (i : ι) (l : Λᵒᵖ),
      (lfpIncl P).map ((rj i).app l) = openSubHom (D.obj l).property.1 (ej i l) := by
    intro i l
    exact P.ι.map_injective (hrj1 i l)
  have hcovAt : ∀ l : Λᵒᵖ, ⨆ i, openAt (W i) l.unop = ⊤ := by
    intro l
    have h : ⨆ i, openAt (W i) l.unop
        = ((D ⋙ (lfpPart P).ι).map
            (homOfLE (bot_le : (⊥ : Λ) ≤ l.unop)).op).left ⁻¹ᵁ (⨆ i, W i) :=
      (Scheme.Hom.preimage_iSup _ _).symm
    rw [h, hWcov]
    simp
  have hstage : ∀ (l : Λᵒᵖ) (y : ∀ i, (lfpRestriction P F).obj (op ((Dj i).obj l))),
      (∀ i k, (lfpRestriction P F).map (lfpOpenLEHom (hle i k l) (ej i l) (ejk i k l)).op (y i)
        = (lfpRestriction P F).map (lfpOpenLEHom (hle' i k l) (ej k l) (ejk i k l)).op (y k)) →
      ∃! z : (lfpRestriction P F).obj (op (D.obj l)),
        ∀ i, (lfpRestriction P F).map ((rj i).app l).op z = y i := by
    intro l y hy
    have hconv : ∀ (z : (lfpRestriction P F).obj (op (D.obj l))) (i : ι),
        (lfpRestriction P F).map ((rj i).app l).op z
          = F.map (openSubHom (D.obj l).property.1 (ej i l)).op z := by
      intro z i
      exact congrArg (fun k : (lfpIncl P).obj ((Dj i).obj l) ⟶ (lfpIncl P).obj (D.obj l) =>
        F.map k.op z) (hrjP i l)
    obtain ⟨z, hz, hzu⟩ := existsUnique_glue_of_isZariskiSheafOnSubcategory haF
      (D.obj l).property.1 (V := fun i => openAt (W i) l.unop) (hcovAt l)
      (A := fun i => (lfpIncl P).obj ((Dj i).obj l)) (fun i => ej i l)
      (V₂ := fun i k => openAt (W i ⊓ W k) l.unop)
      (A₂ := fun i k => (lfpIncl P).obj ((Djk i k).obj l)) (fun i k => ejk i k l)
      (fun i k => hle i k l) (fun i k => hle' i k l)
      (fun i k => by
        rw [hinf i k l, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq])
      y (fun i k => hy i k)
    exact ⟨z, fun i => (hconv z i).trans (hz i),
      fun z' hz' => hzu z' (fun i => (hconv z' i).symm.trans (hz' i))⟩
  have hC3 : ∀ (i k : ι) {j : ι} (l : Λᵒᵖ)
      (h : (π.app (op (⊥ : Λ))).left ⁻¹ᵁ (W i ⊓ W k) ≤ (π.app (op (⊥ : Λ))).left ⁻¹ᵁ W j)
      (hl : openAt (W i ⊓ W k) l.unop ≤ openAt (W j) l.unop),
      (πjk i k).app l ≫ (lfpPart P).ι.map (lfpOpenLEHom hl (ej j l) (ejk i k l))
        = overOpenLE X h ≫ (πj j).app l := by
    intro i k j l h hl
    refine eq_of_comp_openSub_eq (ej j l) ?_
    rw [← hrj1 j l, Category.assoc, ← Functor.map_comp, hC6 i k l hl, hrjk2 i k l,
      Category.assoc, hrj2 j l, ← Category.assoc, overOpenLE_comp_overOpenι]
  have hC4 : ∀ (i k : ι) {j : ι}
      (h : ∀ l : Λᵒᵖ, openAt (W i ⊓ W k) l.unop ≤ openAt (W j) l.unop) {l m : Λᵒᵖ} (φ : l ⟶ m),
      (Djk i k).map φ ≫ lfpOpenLEHom (h m) (ej j m) (ejk i k m)
        = lfpOpenLEHom (h l) (ej j l) (ejk i k l) ≫ (Dj j).map φ := by
    intro i k j h l m φ
    refine lfp_eq_of_comp_eq ((rj j).app m) (hrj1 j m) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z => (Djk i k).map φ ≫ z) (hC6 i k m (h m))) ?_
    refine Eq.trans ((rjk i k).naturality φ) ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (fun z => lfpOpenLEHom (h l) (ej j l) (ejk i k l) ≫ z)
      ((rj j).naturality φ).symm)
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (fun z => z ≫ D.map φ) (hC6 i k l (h l)).symm
  have hy : ∀ (l : Λᵒᵖ) (Z : (lfpRestriction P F).obj (op (D.obj l))) (i k : ι),
      (lfpRestriction P F).map (lfpOpenLEHom (hle i k l) (ej i l) (ejk i k l)).op
          ((lfpRestriction P F).map ((rj i).app l).op Z)
        = (lfpRestriction P F).map (lfpOpenLEHom (hle' i k l) (ej k l) (ejk i k l)).op
          ((lfpRestriction P F).map ((rj k).app l).op Z) := by
    intro l Z i k
    rw [← lfpRestriction_map_comp_apply, ← lfpRestriction_map_comp_apply, hC6 i k l (hle i k l),
      hC6 i k l (hle' i k l)]
  have hrestr : ∀ (l : Λᵒᵖ) (Z : (lfpRestriction P F).obj (op (D.obj l))) (i : ι),
      (affineExtension P F).map (overOpenι X ((π.app (op (⊥ : Λ))).left ⁻¹ᵁ W i)).op
          (affineExtensionι P F (D.obj l) (π.app l) Z)
        = affineExtensionι P F ((Dj i).obj l) ((πj i).app l)
          ((lfpRestriction P F).map ((rj i).app l).op Z) := by
    intro l Z i
    rw [affineExtensionι_naturality, ← hrj2 i l, ← affineExtensionι_map]
  have hpreinf : ∀ i k : ι, (π.app (op (⊥ : Λ))).left ⁻¹ᵁ (W i ⊓ W k)
      = (π.app (op (⊥ : Λ))).left ⁻¹ᵁ W i ⊓ (π.app (op (⊥ : Λ))).left ⁻¹ᵁ W k :=
    fun _ _ => rfl
  have hpreL : ∀ i k : ι, (π.app (op (⊥ : Λ))).left ⁻¹ᵁ (W i ⊓ W k)
      ≤ (π.app (op (⊥ : Λ))).left ⁻¹ᵁ W i := fun i k => (hpreinf i k).le.trans inf_le_left
  have hpreR : ∀ i k : ι, (π.app (op (⊥ : Λ))).left ⁻¹ᵁ (W i ⊓ W k)
      ≤ (π.app (op (⊥ : Λ))).left ⁻¹ᵁ W k := fun i k => (hpreinf i k).le.trans inf_le_right
  intro s hs
  have hex : ∀ i, ∃ (l : Λ) (y : (lfpRestriction P F).obj (op ((Dj i).obj (op l)))),
      affineExtensionι P F ((Dj i).obj (op l)) ((πj i).app (op l)) y = s i := fun i =>
    exists_affineExtensionι_eq_of_isLimit (πj i) (hπj i) (haffj i) (s i)
  choose lj σ hσ using hex
  obtain ⟨l₁, hl₁⟩ := exists_upper_bound lj
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : ∀ i, (lfpRestriction P F).obj (op ((Dj i).obj (op l₁))),
      ∀ i, affineExtensionι P F ((Dj i).obj (op l₁)) ((πj i).app (op l₁)) (σ₁ i) = s i :=
    ⟨fun i => (lfpRestriction P F).map ((Dj i).map (homOfLE (hl₁ i)).op).op (σ i), fun i => by
      rw [affineExtensionι_cone_map (πj i) (homOfLE (hl₁ i)) (σ i)]
      exact hσ i⟩
  have hagree : ∀ i k,
      affineExtensionι P F ((Djk i k).obj (op l₁)) ((πjk i k).app (op l₁))
          ((lfpRestriction P F).map
            (lfpOpenLEHom (hle i k (op l₁)) (ej i (op l₁)) (ejk i k (op l₁))).op (σ₁ i))
        = affineExtensionι P F ((Djk i k).obj (op l₁)) ((πjk i k).app (op l₁))
          ((lfpRestriction P F).map
            (lfpOpenLEHom (hle' i k (op l₁)) (ej k (op l₁)) (ejk i k (op l₁))).op (σ₁ k)) := by
    intro i k
    rw [affineExtensionι_map, affineExtensionι_map, hC3 i k (op l₁) (hpreL i k) (hle i k _),
      hC3 i k (op l₁) (hpreR i k) (hle' i k _), ← affineExtensionι_naturality,
      ← affineExtensionι_naturality, hσ₁ i, hσ₁ k]
    exact hs i k
  have hlater : ∀ i k, ∃ (n : Λ) (hn : l₁ ≤ n),
      (lfpRestriction P F).map ((Djk i k).map (homOfLE hn).op).op
          ((lfpRestriction P F).map
            (lfpOpenLEHom (hle i k (op l₁)) (ej i (op l₁)) (ejk i k (op l₁))).op (σ₁ i))
        = (lfpRestriction P F).map ((Djk i k).map (homOfLE hn).op).op
          ((lfpRestriction P F).map
            (lfpOpenLEHom (hle' i k (op l₁)) (ej k (op l₁)) (ejk i k (op l₁))).op (σ₁ k)) :=
    fun i k => exists_le_map_eq_of_affineExtensionι_eq (πjk i k) (hπjk i k) (haffjk i k) _ _
      (hagree i k)
  choose njk hnjk hjk using hlater
  obtain ⟨n₀, hn₀⟩ := exists_upper_bound (fun p : ι × ι => njk p.1 p.2)
  obtain ⟨m, hl₁m, hn₀m⟩ := exists_ge_ge l₁ n₀
  obtain ⟨σ₂, hσ₂s, hσ₂c⟩ : ∃ σ₂ : ∀ i, (lfpRestriction P F).obj (op ((Dj i).obj (op m))),
      (∀ i, affineExtensionι P F ((Dj i).obj (op m)) ((πj i).app (op m)) (σ₂ i) = s i) ∧
      ∀ i k, (lfpRestriction P F).map
            (lfpOpenLEHom (hle i k (op m)) (ej i (op m)) (ejk i k (op m))).op (σ₂ i)
        = (lfpRestriction P F).map
            (lfpOpenLEHom (hle' i k (op m)) (ej k (op m)) (ejk i k (op m))).op (σ₂ k) := by
    refine ⟨fun i => (lfpRestriction P F).map ((Dj i).map (homOfLE hl₁m).op).op (σ₁ i),
      fun i => ?_, fun i k => ?_⟩
    · rw [affineExtensionι_cone_map (πj i) (homOfLE hl₁m) (σ₁ i)]
      exact hσ₁ i
    · have htr : ∀ Z : (lfpRestriction P F).obj (op ((Djk i k).obj (op l₁))),
          (lfpRestriction P F).map ((Djk i k).map (homOfLE hl₁m).op).op Z
            = (lfpRestriction P F).map
                ((Djk i k).map (homOfLE ((hn₀ (i, k)).trans hn₀m)).op).op
              ((lfpRestriction P F).map ((Djk i k).map (homOfLE (hnjk i k)).op).op Z) :=
        fun Z => (lfpRestriction_map_trans (hnjk i k) ((hn₀ (i, k)).trans hn₀m) Z).symm
      rw [← lfpRestriction_map_comp_apply, ← lfpRestriction_map_comp_apply,
        ← hC4 i k (hle i k) (homOfLE hl₁m).op, ← hC4 i k (hle' i k) (homOfLE hl₁m).op,
        lfpRestriction_map_comp_apply, lfpRestriction_map_comp_apply, htr, htr, hjk i k]
  obtain ⟨z, hz, hzu⟩ := hstage (op m) σ₂ hσ₂c
  refine ⟨affineExtensionι P F (D.obj (op m)) (π.app (op m)) z, fun i => ?_, fun t' ht' => ?_⟩
  · rw [hrestr (op m) z i, hz i]
    exact hσ₂s i
  · obtain ⟨n, z', hz'⟩ := exists_affineExtensionι_eq_of_isLimit π hπ haff t'
    obtain ⟨pp, hmp, hnp⟩ := exists_ge_ge m n
    have hZ : affineExtensionι P F (D.obj (op pp)) (π.app (op pp))
        ((lfpRestriction P F).map (D.map (homOfLE hmp).op).op z)
          = affineExtensionι P F (D.obj (op m)) (π.app (op m)) z :=
      affineExtensionι_cone_map π (homOfLE hmp) z
    have hZ' : affineExtensionι P F (D.obj (op pp)) (π.app (op pp))
        ((lfpRestriction P F).map (D.map (homOfLE hnp).op).op z') = t' := by
      rw [affineExtensionι_cone_map π (homOfLE hnp) z']
      exact hz'
    have hagree2 : ∀ i, affineExtensionι P F ((Dj i).obj (op pp)) ((πj i).app (op pp))
          ((lfpRestriction P F).map ((rj i).app (op pp)).op
            ((lfpRestriction P F).map (D.map (homOfLE hmp).op).op z))
        = affineExtensionι P F ((Dj i).obj (op pp)) ((πj i).app (op pp))
          ((lfpRestriction P F).map ((rj i).app (op pp)).op
            ((lfpRestriction P F).map (D.map (homOfLE hnp).op).op z')) := by
      intro i
      rw [← hrestr (op pp) _ i, ← hrestr (op pp) _ i, hZ, hZ', hrestr (op m) z i, hz i,
        hσ₂s i, ht' i]
    have hlater2 : ∀ i, ∃ (q : Λ) (hq : pp ≤ q),
        (lfpRestriction P F).map ((Dj i).map (homOfLE hq).op).op
            ((lfpRestriction P F).map ((rj i).app (op pp)).op
              ((lfpRestriction P F).map (D.map (homOfLE hmp).op).op z))
          = (lfpRestriction P F).map ((Dj i).map (homOfLE hq).op).op
            ((lfpRestriction P F).map ((rj i).app (op pp)).op
              ((lfpRestriction P F).map (D.map (homOfLE hnp).op).op z')) :=
      fun i => exists_le_map_eq_of_affineExtensionι_eq (πj i) (hπj i) (haffj i) _ _ (hagree2 i)
    choose qi hqi hqeq using hlater2
    obtain ⟨q₀, hq₀⟩ := exists_upper_bound qi
    obtain ⟨q, hpq, hq₀q⟩ := exists_ge_ge pp q₀
    have hpush : ∀ (Z : (lfpRestriction P F).obj (op (D.obj (op pp)))) (i : ι),
        (lfpRestriction P F).map ((rj i).app (op q)).op
            ((lfpRestriction P F).map (D.map (homOfLE hpq).op).op Z)
          = (lfpRestriction P F).map ((Dj i).map (homOfLE hpq).op).op
            ((lfpRestriction P F).map ((rj i).app (op pp)).op Z) :=
      fun Z i => (lfpRestriction_map_app_comm (rj i) (homOfLE hpq) Z).symm
    have hqeq' : ∀ i, (lfpRestriction P F).map ((rj i).app (op q)).op
          ((lfpRestriction P F).map (D.map (homOfLE hpq).op).op
            ((lfpRestriction P F).map (D.map (homOfLE hmp).op).op z))
        = (lfpRestriction P F).map ((rj i).app (op q)).op
          ((lfpRestriction P F).map (D.map (homOfLE hpq).op).op
            ((lfpRestriction P F).map (D.map (homOfLE hnp).op).op z')) := by
      intro i
      rw [hpush, hpush]
      have h1 := lfpRestriction_map_trans (D := Dj i) (hqi i) ((hq₀ i).trans hq₀q)
        ((lfpRestriction P F).map ((rj i).app (op pp)).op
          ((lfpRestriction P F).map (D.map (homOfLE hmp).op).op z))
      have h2 := lfpRestriction_map_trans (D := Dj i) (hqi i) ((hq₀ i).trans hq₀q)
        ((lfpRestriction P F).map ((rj i).app (op pp)).op
          ((lfpRestriction P F).map (D.map (homOfLE hnp).op).op z'))
      rw [← h1, ← h2, hqeq i]
    have hfin := (hstage (op q)
      (fun i => (lfpRestriction P F).map ((rj i).app (op q)).op
        ((lfpRestriction P F).map (D.map (homOfLE hpq).op).op
          ((lfpRestriction P F).map (D.map (homOfLE hmp).op).op z)))
      (hy (op q) _)).unique (fun i => rfl) (fun i => (hqeq' i).symm)
    have hz1 : affineExtensionι P F (D.obj (op q)) (π.app (op q))
        ((lfpRestriction P F).map (D.map (homOfLE hpq).op).op
          ((lfpRestriction P F).map (D.map (homOfLE hmp).op).op z))
        = affineExtensionι P F (D.obj (op m)) (π.app (op m)) z := by
      rw [affineExtensionι_cone_map π (homOfLE hpq), hZ]
    have hz2 : affineExtensionι P F (D.obj (op q)) (π.app (op q))
        ((lfpRestriction P F).map (D.map (homOfLE hpq).op).op
          ((lfpRestriction P F).map (D.map (homOfLE hnp).op).op z')) = t' := by
      rw [affineExtensionι_cone_map π (homOfLE hpq), hZ']
    rw [← hz2, ← hz1, hfin]

end AlgebraicGeometry.ExtendingFunctors

end
